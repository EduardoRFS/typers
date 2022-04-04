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

val make_unit : forall -> Uid.t -> typ
val make_var : forall -> Uid.t -> typ
val make_arrow : forall -> Uid.t -> param:typ -> return:typ -> typ
