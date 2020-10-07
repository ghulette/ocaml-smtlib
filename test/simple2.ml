open Smtlib
open Smtlib_test

let test solv =
  declare_fun solv (Id "int_of_bool") [bool_sort] int_sort;
  assert_ solv (equals (App (Id "int_of_bool", [bool_to_term false])) (int_to_term 0));
  assert_ solv (equals (App (Id "int_of_bool", [bool_to_term true])) (int_to_term 1))

let () =
  run_test test
