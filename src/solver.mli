type t
val z3 : ?path:string -> unit -> t
val command : t -> ('a,'b) Smtlib.command -> 'a -> 'b
