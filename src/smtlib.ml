exception Smtlib_error of string

let smtlib_error msg = raise (Smtlib_error msg)

module Sexp : sig
  type t = Smtlib_syntax.sexp
  val to_channel : out_channel -> t -> unit
  val of_channel : in_channel -> t
end = struct
  type t = Smtlib_syntax.sexp

  let rec write ch =
    let open Smtlib_syntax in function
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

module Solver : sig
  type t
  val z3 : ?path:string -> unit -> t
  val read : t -> Sexp.t
  val write : t -> Sexp.t -> unit
  val command : t -> Sexp.t -> Sexp.t
  val silent_command : t -> Sexp.t -> unit
end = struct
  type t = {
    stdin : out_channel;
    stdout : in_channel;
  }

  let read solver = Sexp.of_channel solver.stdout

  let write solver sexp = Sexp.to_channel solver.stdin sexp

  let command solver sexp =
    write solver sexp;
    read solver

  let silent_command solver sexp =
    write solver sexp

  let print_success_command =
    let open Smtlib_syntax in
    SList [SSymbol "set-option"; SKeyword ":print-success"; SSymbol "true"]

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
      match command solver print_success_command with
        | SSymbol "success" -> solver
        | _ -> smtlib_error "could not configure solver to :print-success"
    with
      Sys_error msg -> smtlib_error ("couldn't talk to solver: " ^ msg)
end


let sexp_to_string sexp =
  let open Buffer in
  let buf = create 100 in
  let rec to_string =
    let open Smtlib_syntax in function
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
  let open Smtlib_syntax in function
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

let id_to_sexp (Id x) = Smtlib_syntax.SSymbol x

let rec sort_to_sexp = function
  | Sort x -> id_to_sexp x
  | SortApp (x, sorts) ->
    SList ((id_to_sexp x) :: (List.map sort_to_sexp sorts))
  | BitVecSort n -> SList [SSymbol "_"; SSymbol "BitVec"; SInt n]

let rec term_to_sexp =
  let open Smtlib_syntax in function
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
  let open Smtlib_syntax in function
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

let expect_success solver sexp =
  match Solver.command solver sexp with
  | SSymbol "success" -> ()
  | SList [SSymbol "error"; SString x] -> smtlib_error x
  | sexp -> smtlib_error ("expected either success or error from solver, got " ^
                     (sexp_to_string sexp))

let declare_const solver id sort =
  expect_success solver
    (SList [SSymbol "declare-const"; id_to_sexp id; sort_to_sexp sort])

let declare_fun solver id args sort =
  expect_success solver
    (SList ([SSymbol "declare-fun"; id_to_sexp id; SList (List.map (fun s -> sort_to_sexp s) args); sort_to_sexp sort]))

let declare_sort solver id arity =
  expect_success solver
    (SList [SSymbol "declare-sort"; id_to_sexp id; SInt arity])

let assert_ solver term =
  expect_success solver (SList [SSymbol "assert"; term_to_sexp term])

let assert_soft solver ?weight:(weight = 1) ?id:(id = "") term =
  let open Smtlib_syntax in
  let id_suffix = match id with
    | "" -> []
    | _ -> [SKeyword ":id"; SSymbol id] in
  let sexp =
    (SList ([SSymbol "assert-soft"; term_to_sexp term; SKeyword ":weight"; SInt weight] @ id_suffix)) in
  Solver.silent_command solver sexp

let maximize solver term =
  Solver.silent_command solver (SList ([SSymbol "maximize"; term_to_sexp term]))

let minimize solver term =
  Solver.silent_command solver (SList ([SSymbol "minimize"; term_to_sexp term]))

let read_objectives solver =
  match Solver.read solver with
  | SList [SSymbol "objectives"; SList _] -> ()
  | s -> smtlib_error ("unexpected result in optimized objective, got " ^ sexp_to_string s)

let check_sat solver =
  let fail sexp  = smtlib_error ("unexpected result from (check-sat), got " ^ sexp_to_string sexp) in
  let rec read_sat sexp =
    let match_map () = match Solver.read solver with
      | SInt _ -> read_sat @@ Solver.read solver
      | sexp -> fail sexp
    in
    match sexp with
    | SSymbol "sat" -> Sat
    | SSymbol "unsat" -> Unsat
    | SSymbol "unknown" -> Unknown
    | SSymbol "|->" -> match_map ()
    | SSymbol _ -> read_sat @@ Solver.read solver
    | SList _ -> read_sat @@ Solver.read solver
    | sexp -> fail sexp
  in
  read_sat @@ Solver.command solver (SList [SSymbol "check-sat"])

let check_sat_using tactic solver =
  let open Smtlib_syntax in
  let fail sexp = smtlib_error ("unexpected result from (check-sat-using), got " ^ sexp_to_string sexp) in
  let rec read_sat sexp =
    let match_map () = match Solver.read solver with
      | SInt _ -> read_sat @@ Solver.read solver
      | sexp -> fail sexp in
    match sexp with
    | SSymbol "sat" -> Sat
    | SSymbol "unsat" -> Unsat
    | SSymbol "unknown" -> Unknown
    | SSymbol "|->" -> match_map ()
    | SSymbol _ -> read_sat @@ Solver.read solver
    | SList _ -> read_sat @@ Solver.read solver
    | sexp -> fail sexp
  in
  let cmd = (SList [SSymbol "check-sat-using"; tactic_to_sexp tactic]) in
  read_sat @@ Solver.command solver cmd

let sexp_error expected sexp =
  smtlib_error ("expected " ^ expected ^ ", but got " ^ sexp_to_string sexp)

type sorted_var = identifier * sort

let sexp_to_sort =
  let open Smtlib_syntax in function
  | SSymbol t -> Sort (Id t)
  | sexp -> sexp_error "sort" sexp

let sexp_to_sorted_var =
  let open Smtlib_syntax in function
  | SList [SSymbol x; sexp] -> Id x, sexp_to_sort sexp
  | sexp -> sexp_error "sorted var" sexp

let sexp_to_model_val =
  let open Smtlib_syntax in function
  | SList [SSymbol "define-fun"; SSymbol x; SList args; s; sexp] ->
    let mv_sort = sexp_to_sort s in
    let mv_term = sexp_to_term sexp in
    let mv_args = List.map sexp_to_sorted_var args in
    Id x, mv_sort, mv_args, mv_term
  | sexp -> sexp_error "model val" sexp

let get_model solver =
  let open Smtlib_syntax in
  let cmd = SList [SSymbol "get-model"] in
  match Solver.command solver cmd with
  | SList (SSymbol "model" :: sexps) -> List.map sexp_to_model_val sexps
  | sexp -> sexp_error "model" sexp

let get_value solver e =
  let open Smtlib_syntax in
  let cmd = SList [SSymbol "get-value"; SList [term_to_sexp e]] in
  match Solver.command solver cmd with
  | SList [SList [_; x]] -> sexp_to_term x
  | sexp -> sexp_error "a single pair" sexp

let push solver = expect_success solver (SList [SSymbol "push"])
let pop solver = expect_success solver (SList [SSymbol "pop"])

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
