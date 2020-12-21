type t =
  | SList of t list
  | SSymbol of string
  | SString of string
  | SKeyword of string
  | SInt of int
  | SBitVec of int * int
  | SBitVec64 of int64

val to_channel : out_channel -> t -> unit

val from_channel : in_channel -> t
