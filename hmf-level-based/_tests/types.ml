type typ = {
  mutable desc : desc;
  mutable forall : forall;
  id : Uid.t;
}
and desc =
  | T_unit
  | T_var
  | T_link  of typ
  | T_arrow of typ * typ
and forall = Level.t ref

let make_typ desc forall id = { desc; forall; id }
let make_unit forall id = make_typ T_unit forall id
let make_var forall id = make_typ T_var forall id
let make_arrow forall id ~param ~return =
  make_typ (T_arrow (param, return)) forall id
