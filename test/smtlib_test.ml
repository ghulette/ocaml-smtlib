open Easy_smt.Smtlib
open Printf

let run_test1 () =
  let solv = make_solver "z3" in
  let x = const "x" in
  let y = const "y" in
  assert_ solv (equals x y);
  assert_ solv (equals x (int_to_term 5));
  assert_ solv (equals y (add x (int_to_term 1)));
  match check_sat solv with
  | Sat -> printf "sat\n"
  | Unsat -> printf "unsat\n"
  | Unknown -> printf "unknown\n"

let () =
  run_test1 ()
