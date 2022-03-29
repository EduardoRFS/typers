module Make (Tree : Tree_s.S) = struct
  include Tree
  module Parser = Parser.Make (Tree)
  let typ_from_string = Lexer.from_string Parser.typ_opt
  let expr_from_string = Lexer.from_string Parser.expr_opt
end
