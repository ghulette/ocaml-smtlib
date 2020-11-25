type t = {
  stdin : out_channel;
  stdout : in_channel;
}

let read solver = Sexp.from_channel solver.stdout

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
