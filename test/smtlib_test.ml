open Easy_smt.Smtlib
open Printf

let term_to_string t = term_to_sexp t |> sexp_to_string

let sort_to_string = function
  | Sort (Id x) -> x
  | _ -> failwith "sort_to_string"

let sorted_var_to_string (Id x, sort) =
  sprintf "%s : %s" x (sort_to_string sort)

let model_value_to_string (Id x) mv =
  let sort = sort_to_string (model_value_sort mv) in
  let term = term_to_string (model_value_term mv) in
  if (model_value_is_const mv) then
    sprintf "%s : %s := %s" x sort term
  else
    let args = List.map sorted_var_to_string (model_value_args mv) in
    sprintf "%s(%s) : %s := %s" x (String.concat ", " args) sort term

let print_result_sat model =
  printf "sat\n";
  let p (x, mv) = printf "%s\n" (model_value_to_string x mv) in
  List.iter p model

let run_test fn =
  let solv = make_solver "z3" in
  fn solv;
  match check_sat solv with
  | Sat ->
    let model = get_model_values solv in
    print_result_sat model
  | Unsat -> printf "unsat\n"
  | Unknown -> printf "unknown\n"
