type level
type t = level

val initial : t
val next : t -> t
val generic : t

val is_weak : t -> bool
val is_generic : t -> bool

val generalize : t -> t
