type t = int
type level = int

(* level : mark : weak  *)

let compare = Int.compare

let is_generic t = t land 0b1 == 0
let is_weak t = t land 0b1 == 0b1

let generalize t = t land -2
let weaken t = t lor 0b1

let mark t = t lor 0b10
let unmark t = t land -3
let is_marked t = t land 0b10 == 0b10

let initial = weaken 0
let increment t = t + 0b100

type offset = int
let offset_from ~base ~to_ =
  let offset = weaken to_ - weaken base in
  assert (offset >= 0);
  offset

let apply_offset off t = t + off

let pp_level fmt level =
  if is_marked level then Format.fprintf fmt "!";
  if is_weak level then Format.fprintf fmt "_";
  Format.fprintf fmt "%d" (level lsr 2)
let show_level = Format.asprintf "%a" pp_level
