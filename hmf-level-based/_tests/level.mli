type level [@@deriving show]
type t = level

val compare : t -> t -> int

val is_generic : t -> bool
val is_weak : t -> bool
val generalize : t -> t
val weaken : t -> t

val mark : t -> t
val unmark : t -> t
val is_marked : t -> bool

val initial : t
val increment : t -> t

type offset
val offset_from : base:t -> to_:t -> offset
val apply_offset : offset -> t -> t
