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

%parameter <Tree : Tree_s.S>
%start <Tree.typ option> typ_opt
%start <Tree.expr option> expr_opt
%%

let with_eof(F) ==
  | v = option(F); EOF; { v }

(* typ *)
let typ_opt := with_eof(typ)

let typ :=
  | typ_atom
  | typ_arrow
  | typ_forall

let typ_atom :=
  | typ_unit
  | typ_var
  | typ_parens

let typ_parens :=
  | LPARENS; typ = typ; RPARENS;
    { typ }

let typ_unit :=
  | UNIT;
    { PT_unit }

let typ_arrow :=
  | param = typ_atom; ARROW; return = typ;
    { PT_arrow (param, return) }

let typ_var :=
  | var = IDENT;
    { PT_var var }

let typ_forall ==
  | FORALL; vars = list(IDENT); DOT; typ = typ;
    { List.fold_left (fun typ var -> PT_forall (var, typ)) typ vars }

(* expr *)

let expr_opt := with_eof(expr)

let expr :=
  | expr_atom
  | expr_let
  | expr_lambda
  | expr_apply

let expr_atom :=
  | expr_unit
  | expr_var
  | expr_parens

let expr_parens :=
  | LPARENS; expr = expr; RPARENS;
    { expr }

let expr_unit :=
  | UNIT;
    { PE_unit }

let expr_var :=
  | var = IDENT;
    { PE_var var }

let expr_let :=
  | LET; var = IDENT; EQUAL; value = expr; IN; body = expr;
    { PE_let (var, value, body) }

let expr_lambda :=
  | FUN; param = IDENT; ARROW; body = expr;
    { PE_lambda (param, None, body) }
  | FUN; LPARENS; param = IDENT; COLON; typ = typ; RPARENS; ARROW; body = expr;
    { PE_lambda (param, Some typ, body) }

let expr_apply :=
  | funct = expr_apply_loop; arg = expr_atom;
    { PE_apply (funct, arg) }
let expr_apply_loop :=
  | expr_apply
  | expr_atom
