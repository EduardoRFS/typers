(* level : weak *)
type level = int
type t = level

let generic = 0b0
let initial = 0b11
let next t = t + 0b10

let is_weak t = t land 0b1 == 1
let is_generic t = t land 0b1 == 0

let generalize t = t land -2
