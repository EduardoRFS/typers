%{ open Tree %}
%token UNIT
%token FUN
%token ARROW
%token LPARENS
%token RPARENS
%token FORALL
%token <string> IDENT
%token DOT
%token COLON
%token LET
%token IN
%token EQUAL
%token EOF

%start <Tree.typ option> typ_opt
%start <Tree.pat option> pat_opt
%start <Tree.expr option> expr_opt
%%

let with_eof(F) ==
  | EOF; { None }
  | v = F; EOF; { Some v }

(* typ *)
let typ_unit ==
  | UNIT; { PT_unit }
let typ_arrow ==
  | t1 = typ_parens; ARROW; t2 = typ; { PT_arrow (t1, t2) }
let typ_var ==
  | i = IDENT; { PT_var i }
let typ_forall ==
  | FORALL; il = list(IDENT); DOT; t = typ;
    { List.fold_left (fun t ident -> PT_forall (ident, t)) t il }

let typ_terminal ==
  | typ_var
  | typ_unit
let typ_parens ==
  | typ_terminal
  | LPARENS; t = typ; RPARENS; { t }

let typ :=
  | typ_parens
  | typ_arrow
  | typ_forall

let typ_opt := with_eof(typ)

(* pat *)
let pat_unit ==
  | UNIT; { PP_unit }
let pat_ident ==
  | i = IDENT; { PP_ident i }
let pat_constraint ==
  | p = pat_parens; COLON; t = typ; { PP_constraint (p, t) }

let pat_terminal ==
  | pat_unit
  | pat_ident
let pat_parens :=
  | pat_terminal
  | LPARENS; p = pat; RPARENS; { p }

let pat :=
  | pat_parens
  | pat_constraint

let pat_opt := with_eof(pat)

(* expr *)

let expr_unit ==
  | UNIT; { PE_unit }
let expr_ident ==
  | i = IDENT; { PE_ident i }
let expr_arrow ==
  | FUN; p = pat_parens; ARROW; e = expr; { PE_arrow (p, e) }
let expr_apply :=
  | e1 = expr_apply_or_parens; e2 = expr_parens; { PE_apply (e1, e2) }
let expr_apply_or_parens ==
  | expr_apply
  | expr_parens
let expr_let ==
  | LET; p = pat; EQUAL; e1 = expr; IN; e2 = expr; { PE_let (p, e1, e2 )}
let expr_constraint ==
  | e = expr_parens; COLON; t = typ; { PE_constraint (e, t) }

let expr_terminal ==
  | expr_unit
  | expr_ident

let expr_parens :=
  | expr_terminal
  | LPARENS; p = expr; RPARENS; { p }

let expr :=
  | expr_parens
  | expr_constraint
  | expr_arrow
  | expr_apply
  | expr_let

let expr_opt := with_eof(expr)
