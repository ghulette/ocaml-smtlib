open Easy_smt.Smtlib
open Smtlib_test

let test1 solv =
  declare_const solv (Id "x") int_sort;
  declare_const solv (Id "y") int_sort;
  let x = const "x" in
  let y = const "y" in
  assert_ solv (equals x (int_to_term 5));
  assert_ solv (equals y (add x (int_to_term 1)))

let () =
  run_test test1
