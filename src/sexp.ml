type t = Sexp_syntax.sexp =
  | SList of t list
  | SSymbol of string
  | SString of string
  | SKeyword of string
  | SInt of int
  | SBitVec of int * int
  | SBitVec64 of int64

let rec write ch = function
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

let from_channel ch =
  let lex = Lexing.from_channel ch in
  Sexp_parser.sexp Sexp_lexer.token lex
