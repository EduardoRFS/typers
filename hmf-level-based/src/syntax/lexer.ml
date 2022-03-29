open Token
open Sedlexing.Utf8

let rec tokenizer buf =
  let whitespace = [%sedlex.regexp? Plus (' ' | '\t' | '\n')] in
  let alpha = [%sedlex.regexp? 'a' .. 'z'] in
  let number = [%sedlex.regexp? '0' .. '9'] in
  let ident = [%sedlex.regexp? (alpha | '_'), Star (alpha | number | '_')] in
  [%sedlex
    match buf with
    | whitespace -> tokenizer buf
    | "forall" -> FORALL
    | "()" -> UNIT
    | "(" -> LPARENS
    | ")" -> RPARENS
    | "." -> DOT
    | "fun" -> FUN
    | "->" -> ARROW
    | "let" -> LET
    | "=" -> EQUAL
    | "in" -> IN
    | ":" -> COLON
    | ident -> IDENT (lexeme buf)
    | eof -> EOF
    | _ -> raise (Invalid_argument "Not a valid token")]
let provider buf () =
  let token = tokenizer buf in
  let start, stop = Sedlexing.lexing_positions buf in
  (token, start, stop)
let from_string parser string =
  let buf = from_string string in
  let provider = provider buf in
  MenhirLib.Convert.Simplified.traditional2revised parser provider
