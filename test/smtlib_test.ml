open Easy_smt.Smtlib
open Printf

let term_to_string t = term_to_sexp t |> sexp_to_string

let print_result_sat model =
  printf "sat\n";
  let p (Id x, t) = printf "%s = %s\n" x (term_to_string t) in
  List.iter p model

let run_test fn =
  let solv = make_solver "z3" in
  fn solv;
  match check_sat solv with
  | Sat ->
      let model = get_model solv in
      print_result_sat model
  | Unsat -> printf "unsat\n"
  | Unknown -> printf "unknown\n"
