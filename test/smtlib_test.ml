open Easy_smt.Smtlib
open Printf

let term_to_string t = term_to_sexp t |> sexp_to_string

let sort_to_string = function
  | Sort (Id x) -> x
  | _ -> failwith "sort_to_string"

let sorted_var_to_string (Id x, sort) =
  sprintf "%s : %s" x (sort_to_string sort)

let model_value_to_string (Id x, sort, args, term) =
  let sort_s = sort_to_string sort in
  let term_s = term_to_string term in
  if List.length args = 0 then
    sprintf "%s : %s := %s" x sort_s term_s
  else
    let args_s = List.map sorted_var_to_string args in
    sprintf "%s(%s) : %s := %s" x (String.concat ", " args_s) sort_s term_s

let print_result_sat model =
  printf "sat\n";
  List.iter (fun mv -> printf "%s\n" (model_value_to_string mv)) model

let run_test fn =
  let solv = make_solver "z3" in
  fn solv;
  match check_sat solv with
  | Sat -> get_model solv |> print_result_sat
  | Unsat -> printf "unsat\n"
  | Unknown -> printf "unknown\n"
