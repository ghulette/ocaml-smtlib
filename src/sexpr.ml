include Sexpr_syntax

(* Does not flush *)
let rec write_sexp out_chan e = match e with
  | SInt n -> output_string out_chan (string_of_int n)
  | SBitVec (n, w) -> Printf.fprintf out_chan "(_ bv%d %d)" n w
  | SBitVec64 n -> Printf.fprintf out_chan "(_ bv%Ld 64)" n
  | SSymbol str -> output_string out_chan str
  | SKeyword str -> output_string out_chan str
  | SString str ->
    (output_char out_chan '(';
     output_string out_chan str;
     output_char out_chan ')')
  | SList lst ->
    (output_char out_chan '(';
     write_sexp_list out_chan lst;
     output_char out_chan ')')

and write_sexp_list (out_chan : out_channel) (es : sexp list) : unit =
  match es with
    | [] -> ()
    | [e] -> write_sexp out_chan e
    | e :: es ->
      (write_sexp out_chan e;
       output_char out_chan ' ';
       write_sexp_list out_chan es)

       (** {1 Low-level interface} *)
