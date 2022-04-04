type uid [@@deriving show]
type t = uid

val initial : t
val next : t -> t

val compare : t -> t -> int
