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

(* level *)
type level_content =
  | Weak    of int
  | Generic
type level = level_content ref

let is_generic level =
  match !level with
  | Weak _ -> false
  | Generic -> true
let is_weak level =
  match !level with
  | Weak _ -> true
  | Generic -> false

let initial_level_counter = 0
let current_level_counter = ref initial_level_counter
let level_stack : level Stack.t = Stack.create ()
let enter_level () =
  incr current_level_counter;
  Stack.push (ref (Weak !current_level_counter)) level_stack
let leave_level () =
  decr current_level_counter;
  let level = Stack.pop level_stack in
  level := Generic
let reset_level () =
  Stack.clear level_stack;
  current_level_counter := initial_level_counter
let current_level () = Stack.top level_stack

(* forall *)
type forall =
  | Forall      of level
  | Forall_link of level

let level forall =
  match forall with
  | Forall level -> level
  | Forall_link level -> level
let has_forall forall =
  match forall with
  | Forall level -> is_generic level
  | Forall_link _level -> false
let is_generic forall = is_generic (level forall)
let is_weak forall = is_weak (level forall)

(* typ *)
type typ = {
  mutable forall : forall;
  mutable desc : desc;
}
and desc =
  | T_unit
  | T_arrow of typ * typ
  | T_var
  | T_link  of typ

let rec repr typ =
  (* TODO: path compression*)
  match typ.desc with
  | T_link typ -> repr typ
  | _ -> typ

let forall typ = (repr typ).forall
let level typ = level (forall typ)
let desc typ = (repr typ).desc

let has_forall typ = has_forall (forall typ)
let is_generic typ = is_generic (forall typ)
let is_weak typ = is_weak (forall typ)
let same a b = repr a == repr b

let make forall desc = { forall; desc }
let make_unit forall = make forall T_unit
let make_var forall = make forall T_var
let make_arrow forall (param, return) = make forall (T_arrow (param, return))

let new_unit () = make_unit (Forall_link (current_level ()))
let new_var () = make_var (Forall_link (current_level ()))
let new_arrow (param, return) =
  make_arrow (Forall_link (current_level ())) (param, return)

(* copy and instance *)
(* this makes a perfect copy of the graph *)
let rec copy foralls types typ =
  (* weak may contain generic *)
  if is_generic typ then
    copy_uniq foralls types typ
  else
    typ

and copy_uniq foralls types typ =
  match List.assq_opt typ !types with
  | Some typ -> typ
  | None ->
    let typ' = copy_forall foralls types typ in
    types := (typ, typ') :: !types;
    typ'

and copy_forall foralls types typ =
  let level = level typ in
  let foralls, forall =
    if has_forall typ then
      let level' = ref Generic in
      (* level physical identity *)
      let foralls = (level, level') :: foralls in
      let forall = Forall level' in
      (foralls, forall)
    else
      let level' = List.assq level foralls in
      let forall = Forall_link level' in
      (foralls, forall) in
  copy_desc foralls types ~forall typ

and copy_desc foralls types ~forall typ =
  let copy typ = copy foralls types typ in
  match desc typ with
  | T_unit -> make_unit forall
  | T_arrow (param, return) ->
    let param = copy param in
    let return = copy return in
    make_arrow forall (param, return)
  | T_var -> make_var forall
  | T_link _ -> assert false
let copy typ =
  let types = [] in
  let foralls = ref [] in
  copy types foralls typ

let instance typ =
  if is_generic typ then (
    assert (has_forall typ);

    (* top forall points to current level *)
    let level = level typ in
    let level' = current_level () in
    let foralls = [(level, level')] in
    let types = ref [] in
    let forall = Forall_link level' in
    copy_desc foralls types ~forall typ)
  else
    typ

(* unify *)
exception Occurs_check
exception Escape_check
exception Type_clash

let is_weak_var typ =
  match desc typ with
  | T_var -> is_weak typ
  | T_unit
  | T_arrow _ ->
    false
  | T_link _ -> assert false
let rec unify ~expected ~received =
  if same expected received then
    ()
  else
    unify_vars ~expected ~received

and unify_vars ~expected ~received =
  if is_weak_var expected then
    unify_var ~var:expected ~typ:received
  else if is_weak_var received then
    unify_var ~var:received ~typ:expected
  else
    unify_forall ~expected ~received

and unify_forall ~expected ~received =
  enter_level ();
  let received =
    (* it is okay for received to be weakened with this big level because
       a received weak variable will be unified with a generic type, in which
       case the level doesn't matter

       or it will be unified with a weak type, in which case it will have
       a smaller level, making it go the other forall
    *)
    if has_forall received then instance received else received in
  ()

and unify_constructor ~expected ~received =
  match (desc expected, desc received) with
  | T_unit, T_unit -> ()
  | ( T_arrow (expected_param, expected_return),
      T_arrow (received_param, received_return) ) ->
    unify ~expected:received_param ~received:expected_param;
    unify ~expected:expected_return ~received:received_return
  | _, T_var ->
    (* received: forall a. a *)
    (* TODO: this clearly seems weird *)
    unify_var ~var:received ~typ:expected
  | _ -> raise Type_clash

and unify_var ~var ~typ = assert false
