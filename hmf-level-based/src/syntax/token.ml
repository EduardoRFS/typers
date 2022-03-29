type token =
  | UNIT
  | FUN
  | ARROW
  | LPARENS
  | RPARENS
  | FORALL
  | IDENT   of string
  | DOT
  | COLON
  | LET
  | IN
  | EQUAL
  | EOF
