(* syntax *)
module Tree = struct
  type var = string
  and typ =
    | PT_unit
    | PT_arrow  of typ * typ
    | PT_var    of var
    | PT_forall of var * typ
  and expr =
    | PE_unit
    | PE_var    of var
    | PE_let    of var * expr * expr
    | PE_lambda of var * typ option * expr
    | PE_apply  of expr * expr
  [@@deriving show { with_path = false }]
end
open Tree

(* type machinery *)
exception Occurs_check
exception Escape_check
exception Type_clash

module Level : sig
  type level
  type t = level

  val generic : t

  val current_level : unit -> t
  val enter_level : unit -> unit
  val leave_level : unit -> unit
  val reset_level : unit -> unit

  val is_weak : t -> bool
  val is_generic : t -> bool

  val generalize : t -> t
end = struct
  (* level : weak *)
  type level = int
  type t = level

  let generic = 0b0
  let initial = 0b11

  let current_level = ref initial
  let enter_level () = current_level := !current_level + 0b10
  let leave_level () = current_level := !current_level - 0b10
  let reset_level () = current_level := initial
  let current_level () = !current_level

  let is_weak t = t land 0b1 == 1
  let is_generic t = t land 0b1 == 0

  let generalize t = t land -2
end
open Level
type forall =
  | Forall      of level ref
  | Forall_link of level ref
and typ = {
  mutable forall : forall;
  mutable desc : desc;
}
and desc =
  | T_unit
  | T_arrow of typ * typ
  | T_var
  | T_link  of typ

(* Possible to guarantee that all Forall are generic *)
let forall_stack = Stack.create ()
let enter_forall () =
  enter_level ();
  let level_ref = ref (current_level ()) in
  Stack.push level_ref forall_stack
let leave_forall () =
  leave_level ();
  let level_ref = Stack.pop forall_stack in
  Forall level_ref
let current_forall () = Stack.top forall_stack

let make_typ forall desc = { forall; desc }
let make_unit forall = make_typ forall T_unit
let make_arrow forall (param, return) =
  make_typ forall (T_arrow (param, return))
let make_var forall = make_typ forall T_var

let rec repr typ =
  (* TODO: path compression*)
  match typ.desc with
  | T_link typ -> repr typ
  | _ -> typ

let level_ref forall =
  match forall with
  | Forall level_ref
  | Forall_link level_ref ->
    level_ref

let level forall = !(level_ref forall)

let is_generic forall =
  let level_ref = level_ref forall in
  is_generic !level_ref
let is_weak forall =
  let level_ref = level_ref forall in
  is_weak !level_ref

let generic_tag forall =
  let level_ref = level_ref forall in
  level_ref := Level.generalize (current_level ())
let generic_untag forall =
  let level_ref = level_ref forall in
  level_ref := generic
let is_generic_tagged forall = level forall = generic

let has_forall typ =
  match typ.forall with
  | Forall _ ->
    (* if it has Forall, then it must be generic *)
    true
  | Forall_link _ -> false

(*
Problem with unification a type with the same forall apearing
twice can be created, such as:

- (forall a[0]. a) -> (forall a[0]. a) -> ()
This means when unifying generic types on the received side must be instantiated.

It's possible to make so that copying will never create this, but this still
needs to be handled somehow, any optimziation is possible here?.
*)

let make forall desc = { forall; desc }
let unit () = T_unit
let var () = T_var
let arrow (param, return) = T_arrow (param, return)

let new_unit () = assert false
let new_var () = assert false
let new_arrow _ = assert false

let generalize () =
  let forall = current_forall () in
  forall := generic

let rec copy foralls typ =
  let typ = repr typ in

  (* weak may contain generic *)
  if is_generic typ.forall then
    copy_forall foralls typ
  else
    typ

and copy_forall foralls typ =
  let level_ref = level_ref typ.forall in
  if has_forall typ then
    let level_ref' = ref !level_ref in
    let foralls = (level_ref, (level_ref', ref [])) :: foralls in
    let forall = Forall level_ref' in
    copy_desc foralls ~forall typ
  else
    let level_ref, types = List.assq level_ref foralls in
    let forall = Forall_link level_ref in
    copy_uniq foralls types ~forall typ

and copy_uniq foralls types ~forall typ =
  match List.assq_opt typ !types with
  | Some typ -> typ
  | None ->
    let typ' = copy_desc foralls ~forall typ in
    types := (typ, typ') :: !types;
    typ'

and copy_desc foralls ~forall typ =
  let copy typ = copy foralls typ in
  match typ.desc with
  | T_unit -> make_unit forall
  | T_arrow (param, return) ->
    let param = copy param in
    let return = copy return in
    make_arrow forall (param, return)
  | T_var -> make_var forall
  | T_link _ -> assert false
let copy typ = copy [] typ
let instance typ =
  let typ = repr typ in
  if is_generic typ.forall then
    let level_ref = level_ref typ.forall in
    let level_ref' = current_forall () in
    let foralls = [(level_ref, (level_ref', ref []))] in
    let forall = Forall_link level_ref' in
    copy_desc foralls ~forall typ
  else
    typ

(* check for recursive bindings, update the levels *)
(* find smallest weak forall *)
let rec min_forall forall_ref typ =
  let min_forall typ = min_forall forall_ref typ in
  let typ = repr typ in

  if is_weak typ.forall then
    if level typ.forall < level !forall_ref then
      forall_ref := typ.forall;

  match typ.desc with
  | T_unit -> ()
  | T_arrow (param, return) ->
    min_forall param;
    min_forall return
  | T_var -> ()
  | T_link _ -> assert false
let min_forall forall typ =
  let forall_ref = ref forall in
  min_forall forall_ref typ;
  !forall_ref

let rec update_forall forall typ =
  let update_forall typ = update_forall forall typ in
  let typ = repr typ in

  if is_weak typ.forall then
    typ.forall <- forall;

  match typ.desc with
  | T_unit -> ()
  | T_arrow (param, return) ->
    update_forall param;
    update_forall return
  | T_var -> ()
  | T_link _ -> assert false

(* TODO: better name, root means the var being unified *)
let rec occurs root typ =
  let occurs typ = occurs root typ in

  (* physical equality *)
  if root == typ then
    raise Occurs_check;

  match typ.desc with
  | T_link typ -> occurs typ
  | T_unit -> ()
  | T_arrow (param, return) ->
    occurs param;
    occurs return
  | T_var -> ()

let rec escapes min_level typ =
  let escapes typ = escapes min_level typ in
  let typ = repr typ in

  if has_forall typ then
    generic_untag typ.forall;

  (if is_generic_tagged typ.forall then
     let forall_level = level typ.forall in
     (* TODO: the level must be equal? *)
     if min_level <> forall_level then
       raise Escape_check);

  match typ.desc with
  | T_unit -> ()
  | T_arrow (param, return) ->
    escapes param;
    escapes return
  | T_var -> ()
  | T_link _ -> assert false

let with_forall f =
  enter_forall ();
  let typ = f () in
  generalize ();
  let forall = leave_forall () in
  typ.forall <- forall;
  typ

let is_weak_var typ =
  match typ.desc with
  | T_var -> is_weak typ.forall
  | T_unit
  | T_arrow _ ->
    false
  | T_link _ -> assert false

let unify_var ~var ~typ =
  if is_generic var.forall then
    raise Escape_check;

  let forall = min_forall var.forall typ in
  update_forall forall typ;
  occurs var typ;
  escapes (level forall) typ;
  var.desc <- T_link typ

(* TODO: maybe subtype should return something?*)
let rec subtype ~expected ~received =
  let expected = repr expected in
  let received = repr received in
  (* physical identity *)
  if expected == received then
    ()
  else
    subtype_vars ~expected ~received

and subtype_vars ~expected ~received =
  if is_weak_var expected then
    unify_var ~var:expected ~typ:received
  else if is_weak_var received then
    unify_var ~var:received ~typ:expected
  else
    subtype_forall ~expected ~received

and subtype_forall ~expected ~received =
  enter_forall ();
  if has_forall expected then
    (* TODO: is tagging like this okay? *)
    (* TODO: if rectype exists? *)
    generic_tag expected.forall;

  (* it is okay for received to be weakened with this big level because
     a received weak variable will be unified with a generic type, in which
     case the level doesn't matter

     or it will be unified with a weak type, in which case it will have
     a smaller level, making it go the other forall
  *)
  if has_forall received then
    let received = instance received in
    (* TODO: this is hackish *)
    if is_weak_var received then
      unify_var ~var:received ~typ:expected
    else
      subtype_simple ~expected ~received
  else
    subtype_simple ~expected ~received;

  (* TODO: any usage for this forall? *)
  let _forall = leave_forall () in
  ()

and subtype_simple ~expected ~received =
  match (expected.desc, received.desc) with
  | T_unit, T_unit -> ()
  | ( T_arrow (expected_param, expected_return),
      T_arrow (received_param, received_return) ) ->
    subtype ~expected:received_param ~received:expected_param;
    subtype ~expected:expected_return ~received:received_return
  | _ -> raise Type_clash

(* typer *)
let rec transl env typ =
  match typ with
  | PT_unit -> new_unit ()
  | PT_arrow (param, return) ->
    let param = transl env param in
    let return = transl env return in
    new_arrow (param, return)
  | PT_forall _ ->
    with_forall @@ fun () ->
    generalize ();
    transl_forall_loop env typ
  | PT_var var -> List.assoc var env

and transl_forall_loop env typ =
  match typ with
  | PT_forall (var, body) ->
    let var_typ = new_var () in
    let env = (var, var_typ) :: env in
    transl_forall_loop env body
  | typ -> transl env typ

let transl typ = transl [] typ

let rec infer env expr =
  match expr with
  | PE_unit -> new_unit ()
  | PE_var var -> List.assoc var env
  | PE_let (var, value, body) ->
    let value_typ = infer env value in
    let env = (var, value_typ) :: env in
    infer env body
  | PE_lambda (param, param_typ, body) ->
    with_forall @@ fun () ->
    let param_typ =
      match param_typ with
      | Some param_typ -> transl param_typ
      | None -> new_var () in
    let body_typ =
      let env = (param, param_typ) :: env in
      let body_typ = infer env body in
      instance body_typ in
    new_arrow (param_typ, body_typ)
  | PE_apply (funct, arg) ->
    let funct_typ = infer env funct in
    let arg_typ = infer env arg in
    let return_typ = new_var () in
    let expected_typ = new_arrow (arg_typ, return_typ) in
    subtype ~expected:expected_typ ~received:funct_typ;
    return_typ
