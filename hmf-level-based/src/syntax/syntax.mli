module Make (Tree : Tree_s.S) : sig
  include module type of Tree
  val typ_from_string : string -> Tree.typ option
  val expr_from_string : string -> Tree.expr option
end
