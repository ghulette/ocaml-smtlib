open Easy_smt.Smtlib
open Printf

let term_to_string t = term_to_sexp t |> sexp_to_string

let run_test1 () =
  let solv = make_solver "z3" in
  declare_const solv (Id "x") (Sort (Id "Int"));
  declare_const solv (Id "y") (Sort (Id "Int"));
  let x = const "x" in
  let y = const "y" in
  assert_ solv (equals x (int_to_term 5));
  assert_ solv (equals y (add x (int_to_term 1)));
  match check_sat solv with
  | Sat ->
      let model = get_model solv in
      let p (Id x, t) = printf "%s = %s\n" x (term_to_string t) in
      List.iter p model
  | Unsat -> printf "unsat\n"
  | Unknown -> printf "unknown\n"

let () =
  run_test1 ()
