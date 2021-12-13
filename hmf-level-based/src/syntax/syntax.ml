include Tree

let typ_from_string = Lexer.from_string Parser.typ_opt
let pat_from_string = Lexer.from_string Parser.pat_opt
let expr_from_string = Lexer.from_string Parser.expr_opt
