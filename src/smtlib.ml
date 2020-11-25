exception Smtlib_error of string

let smtlib_error msg = raise (Smtlib_error msg)

module Sexp = struct
  type t = Smtlib_syntax.sexp =
    | SList of t list
    | SSymbol of string
    | SString of string
    | SKeyword of string
    | SInt of int
    | SBitVec of int * int
    | SBitVec64 of int64

  let rec write ch = function
    | SInt n -> Printf.fprintf ch "%d" n
    | SBitVec (n, w) -> Printf.fprintf ch "(_ bv%d %d)" n w
    | SBitVec64 n -> Printf.fprintf ch "(_ bv%Ld 64)" n
    | SSymbol str -> output_string ch str
    | SKeyword str -> output_string ch str
    | SString str -> Printf.fprintf ch "(%s)" str
    | SList lst -> Printf.fprintf ch "(%a)" write_list lst

  and write_list out_chan = function
    | [] -> ()
    | [e] -> write out_chan e
    | e :: es ->
      Printf.fprintf out_chan "%a " write e;
      write_list out_chan es

  let to_channel ch sexp = Printf.fprintf ch "%a\n%!" write sexp

  let of_channel ch =
    let lex = Lexing.from_channel ch in
    Smtlib_parser.sexp Smtlib_lexer.token lex
end

type ('inp,'outp) command = ('inp -> Sexp.t) * (Sexp.t -> 'outp)

module Solver : sig
  type t
  val z3 : ?path:string -> unit -> t
  val command : t -> ('a,'b) command -> 'a -> 'b
end = struct
  type t = {
    stdin : out_channel;
    stdout : in_channel;
  }

  let read solver = Sexp.of_channel solver.stdout

  let write solver sexp = Sexp.to_channel solver.stdin sexp

  let command solver (inp,outp) x =
    let in_sexp = inp x in
    write solver in_sexp;
    let out_sexp = read solver in
    outp out_sexp

  let print_success_command =
    let open Sexp in
    let inp () = SList [SSymbol "set-option"; SKeyword ":print-success"; SSymbol "true"] in
    let outp = function
      | SSymbol "success" -> ()
      | _ -> smtlib_error "could not configure solver to :print-success"
    in
    (inp,outp)

  (* keep track of all solvers we spawn, so we can close our read/write
    FDs when the solvers exit *)
  let _solvers : (int * t) list ref = ref []

  let () =
    let handle_sigchild _ =
      if List.length !_solvers = 0
      then Unix.waitpid [] (-1) |> ignore
      else
        begin
          let (pid, _) = Unix.waitpid [] (-1) in
          Printf.eprintf "solver child (pid %d) exited\n%!" pid;
          try
            let solver = List.assoc pid !_solvers in
            close_in_noerr solver.stdout;
            close_out_noerr solver.stdin;
            _solvers := List.remove_assoc pid !_solvers
          with
            _ -> ()
        end
    in
    Sys.set_signal Sys.sigchld (Sys.Signal_handle handle_sigchild)

  let z3 ?(path="z3") () =
    let open Unix in
    let (z3_stdin, z3_stdin_writer) = pipe () in
    let (z3_stdout_reader, z3_stdout) = pipe () in
    (* If the ocaml ends of the pipes aren't marked close-on-exec, they
      will remain open in the fork/exec'd z3 process, and z3 won't exit
      when our main ocaml process ends. *)
    set_close_on_exec z3_stdin_writer;
    set_close_on_exec z3_stdout_reader;
    let pid = create_process path [| path; "-in"; "-smt2" |]
      z3_stdin z3_stdout stderr in
    let in_chan = in_channel_of_descr z3_stdout_reader in
    let out_chan = out_channel_of_descr z3_stdin_writer in
    set_binary_mode_out out_chan false;
    set_binary_mode_in in_chan false;
    let solver = {
      stdin = out_chan;
      stdout = in_chan
    } in
    _solvers := (pid, solver) :: !_solvers;
    try
      command solver print_success_command ();
      solver
    with
      Sys_error msg -> smtlib_error ("couldn't talk to solver: " ^ msg)
end


let sexp_to_string sexp =
  let open Buffer in
  let buf = create 100 in
  let rec to_string =
    let open Sexp in function
    | SList alist -> add_char buf '('; list_to_string alist; add_char buf ')'
    | SSymbol x -> add_string buf x;
    | SKeyword x -> add_string buf x;
    | SString x -> add_char buf '"'; add_string buf x; add_char buf '"'
    | SInt n -> add_string buf (string_of_int n)
    | SBitVec (n, w) -> add_string buf (Format.sprintf "(_ bv%d %d)" n w)
    | SBitVec64 n -> add_string buf (Format.sprintf "(_ bv%Ld 64)" n)
  and list_to_string = function
    | [] -> ()
    | [x] -> to_string x
    | x :: xs -> to_string x; add_char buf ' '; list_to_string xs in
  to_string sexp;
  contents buf

type check_sat_result =
  | Sat
  | Unsat
  | Unknown

type identifier =
  | Id of string

type sort =
  | Sort of identifier
  | SortApp of identifier * sort list
  | BitVecSort of int

type term =
  | String of string
  | Int of int
  | BitVec of int * int
  | BitVec64 of int64
  | Const of identifier
  | App of identifier * term list
  | Let of string * term * term

type tactic =
  | Simplify
  | SolveEQs
  | BitBlast
  | AIG
  | SAT
  | SMT
  | QFBV
  | UsingParams of tactic * (string * bool) list
  | Then of tactic list

let rec tactic_to_sexp =
  let open Sexp in function
  | Simplify -> SSymbol "simplify"
  | SolveEQs -> SSymbol "solve-eqs"
  | BitBlast -> SSymbol "bit-blast"
  | AIG -> SSymbol "aig"
  | SAT -> SSymbol "sat"
  | SMT -> SSymbol "smt"
  | QFBV -> SSymbol "qfbv"
  | UsingParams (t', params) ->
    let param_to_sexp (keyword, value) =
      [ SKeyword keyword; SSymbol (string_of_bool value) ] in
    SList ((SSymbol "using-params") :: (tactic_to_sexp t')
           :: (List.concat_map param_to_sexp params))
  | Then ts ->
    SList ((SSymbol "then") :: List.map tactic_to_sexp ts)

let id_to_sexp (Id x) = Sexp.SSymbol x

let rec sort_to_sexp = function
  | Sort x -> id_to_sexp x
  | SortApp (x, sorts) ->
    SList ((id_to_sexp x) :: (List.map sort_to_sexp sorts))
  | BitVecSort n -> SList [SSymbol "_"; SSymbol "BitVec"; SInt n]

let rec term_to_sexp =
  let open Sexp in function
  | String s -> SString s
  | Int n -> SInt n
  | BitVec (n, w) -> SBitVec (n, w)
  | BitVec64 n -> SBitVec64 n
  | Const x -> id_to_sexp x
  | App (f, args) -> SList (id_to_sexp f :: List.map term_to_sexp args)
  | Let (x, t1, t2) ->
    SList [SSymbol "let";
           SList [SList [SSymbol x; term_to_sexp t1]];
           term_to_sexp t2]

let rec sexp_to_term =
  let open Sexp in function
  | SString s -> String s
  | SInt n -> Int n
  | SBitVec (n, w) -> BitVec (n, w)
  | SBitVec64 n -> BitVec64 n
  | SSymbol x -> Const (Id x)
  | SList (SSymbol "-" :: SInt x :: []) -> Int (-x)
  | SList (SSymbol f::args) ->
    let ts = List.map sexp_to_term args in
    App (Id f, ts)
  | sexp -> smtlib_error ("unparseable term " ^ sexp_to_string sexp)

let expect_success inp : ('a,unit) command =
  let open Sexp in
  let outp = function
    | SSymbol "success" -> ()
    | SList [SSymbol "error"; SString x] -> smtlib_error x
    | sexp -> smtlib_error ("expected either success or error from solver, got " ^
                           (sexp_to_string sexp))
  in (inp,outp)

let declare_const_command =
  expect_success
    (fun (id,sort) -> SList [SSymbol "declare-const"; id_to_sexp id; sort_to_sexp sort])

let declare_const solver id sort =
  Solver.command solver declare_const_command (id,sort)

let declare_fun_command =
  expect_success
    (fun (id,args,sort) -> SList ([SSymbol "declare-fun"; id_to_sexp id; SList (List.map sort_to_sexp args); sort_to_sexp sort]))

let declare_fun solver id args sort =
  Solver.command solver declare_fun_command (id,args,sort)

let declare_sort_command =
  expect_success
    (fun (id,arity) -> SList [SSymbol "declare-sort"; id_to_sexp id; SInt arity])

let declare_sort solver id arity =
  Solver.command solver declare_sort_command (id,arity)

let assert_command =
  expect_success (fun term -> SList [SSymbol "assert"; term_to_sexp term])

let assert_ solver term =
  Solver.command solver assert_command term

let assert_soft_command =
  let open Sexp in
  let inp (weight,id_opt,term) =
    let id_suf =
      match id_opt with
      | None -> []
      | Some (Id x) -> [SKeyword ":id"; SSymbol x]
    in
    SList ([SSymbol "assert-soft"; term_to_sexp term; SKeyword ":weight"; SInt weight] @ id_suf)
  in
  expect_success inp

let assert_soft solver ?(weight = 1) ?id term =
  Solver.command solver assert_soft_command (weight,id,term)

let maximize_command =
  expect_success (fun term -> SList ([SSymbol "maximize"; term_to_sexp term]))

let maximize solver term =
  Solver.command solver maximize_command term

let minimize_command =
  expect_success (fun term -> SList ([SSymbol "minimize"; term_to_sexp term]))

let minimize solver term =
  Solver.command solver minimize_command term

let get_objectives_command =
  let open Sexp in
  let inp () = SList [SSymbol "get-objectives"] in
  let outp = function
    | SList [SSymbol "objectives"; SList _] -> ()
    | s -> smtlib_error ("unexpected result in optimized objective, got " ^ sexp_to_string s)
  in
  (inp,outp)

let get_objectives solver =
  Solver.command solver get_objectives_command ()

let sat_result_of_sexp =
  let open Sexp in function
  | SSymbol "sat" -> Sat
  | SSymbol "unsat" -> Unsat
  | SSymbol "unknown" -> Unknown
  | sexp -> smtlib_error ("unexpected result from (check-sat), got " ^ sexp_to_string sexp)

let check_sat_command =
  let inp () = Sexp.(SList [SSymbol "check-sat"]) in
  (inp,sat_result_of_sexp)

let check_sat solver =
  Solver.command solver check_sat_command ()

let check_sat_using_command =
  let inp tactic = Sexp.(SList [SSymbol "check-sat-using"; tactic_to_sexp tactic]) in
  (inp, sat_result_of_sexp)

let check_sat_using tactic solver =
  Solver.command solver check_sat_using_command tactic

let sexp_error expected sexp =
  smtlib_error ("expected " ^ expected ^ ", but got " ^ sexp_to_string sexp)

type sorted_var = identifier * sort

let sexp_to_sort =
  let open Sexp in function
  | SSymbol t -> Sort (Id t)
  | sexp -> sexp_error "sort" sexp

let sexp_to_sorted_var =
  let open Sexp in function
  | SList [SSymbol x; sexp] -> Id x, sexp_to_sort sexp
  | sexp -> sexp_error "sorted var" sexp

let sexp_to_model_val =
  let open Sexp in function
  | SList [SSymbol "define-fun"; SSymbol x; SList args; s; sexp] ->
    let mv_sort = sexp_to_sort s in
    let mv_term = sexp_to_term sexp in
    let mv_args = List.map sexp_to_sorted_var args in
    Id x, mv_sort, mv_args, mv_term
  | sexp -> sexp_error "model val" sexp

let get_model_command =
  let open Sexp in
  let inp () = SList [SSymbol "get-model"] in
  let outp = function
    | SList (SSymbol "model" :: sexps) -> List.map sexp_to_model_val sexps
    | sexp -> sexp_error "model" sexp
  in
  (inp,outp)

let get_model solver =
  Solver.command solver get_model_command ()

let get_value_command =
  let open Sexp in
  let inp term = SList [SSymbol "get-value"; SList [term_to_sexp term]] in
  let outp = function
    | SList [SList [_; x]] -> sexp_to_term x
    | sexp -> sexp_error "a single pair" sexp
  in
  (inp,outp)

let get_value solver term =
  Solver.command solver get_value_command term

let push_command =
  expect_success (fun () -> Sexp.(SList [SSymbol "push"]))

let push solver =
  Solver.command solver push_command ()

let pop_command =
  expect_success (fun () -> Sexp.(SList [SSymbol "pop"]))

let pop solver =
  Solver.command solver pop_command ()

let int_sort  = Sort (Id "Int")

let bool_sort = Sort (Id "Bool")

let array_sort dom rng = SortApp (Id "Array", [dom; rng])

let bv_sort w = BitVecSort w

let int_to_term n = Int n

let const x = Const (Id x)

let bool_to_term b = match b with
  | true -> Const (Id "true")
  | false -> Const (Id "false")

let app2 x term1 term2 = App (Id x, [term1; term2])

let app1 x term = App (Id x, [term])

let equals = app2 "="

let and_ term1 term2 = match (term1, term2) with
  | (App (Id "and", alist1), App (Id "and", alist2)) -> App (Id "and", alist1 @ alist2)
  | (App (Id "and", alist1), _) -> App (Id "and", alist1 @ [ term2 ])
  | (_, App (Id "and", alist2)) -> App (Id "and", term1 :: alist2)
  | _ -> App (Id "and", [term1; term2])

let or_ term1 term2 = match (term1, term2) with
  | (App (Id "or", alist1), App (Id "or", alist2)) -> App (Id "or", alist1 @ alist2)
  | (App (Id "or", alist1), _) -> App (Id "or", alist1 @ [ term2 ])
  | (_, App (Id "or", alist2)) -> App (Id "or", term1 :: alist2)
  | _ -> App (Id "or", [term1; term2])

let xor term1 term2 = match term1, term2 with
  | (App (Id "xor", alist1), App (Id "xor", alist2)) -> App (Id "xor", alist1 @ alist2)
  | (App (Id "xor", alist1), _) -> App (Id "xor", alist1 @ [ term2 ])
  | (_, App (Id "xor", alist2)) -> App (Id "xor", term1 :: alist2)
  | _ -> App (Id "xor", [term1; term2])

let not_ term = App (Id "not", [term])
let ite e1 e2 e3 = App (Id "ite", [e1; e2; e3])
let implies = app2 "=>"
let add = app2 "+"
let sub = app2 "-"
let mul = app2 "*"
let lt = app2 "<"
let gt = app2 ">"
let lte = app2 "<="
let gte = app2 ">="

let bv n w = BitVec (n, w)
let bv64 n = BitVec64 n

let bvadd  = app2 "bvadd"
let bvsub  = app2 "bvsub"
let bvmul  = app2 "bvmul"
let bvurem = app2 "bvurem"
let bvsrem = app2 "bvsrem"
let bvsmod = app2 "bvsmod"
let bvshl  = app2 "bvshl"
let bvlshr = app2 "bvlshr"
let bvashr = app2 "bvashr"
let bvor   = app2 "bvor"
let bvand  = app2 "bvand"
let bvnand = app2 "bvnand"
let bvnor  = app2 "bvnor"
let bvxnor = app2 "bvxnor"
let bvudiv = app2 "bvudiv"
let bvsdiv = app2 "bvsdiv"
let bvugt  = app2 "bvugt"
let bvuge  = app2 "bvuge"
let bvult  = app2 "bvult"
let bvule  = app2 "bvule"
let bvneg  = app1 "bvneg"
let bvnot  = app1 "bvnot"
