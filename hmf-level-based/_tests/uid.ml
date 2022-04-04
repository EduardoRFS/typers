type t = int [@@deriving show]
type uid = t [@@deriving show]

let initial = 0

(* TODO: this only works in parallel on x86 *)
let next t = t + 1

let compare = Int.compare
