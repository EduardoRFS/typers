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

type level = int
and forall = { mutable forall_desc : forall_desc }
and forall_desc =
  | Forall      of {
      mutable generic : bool;
      mutable level : level;
    }
  (* TODO: can link be avoided? *)
  | Forall_link of forall
and typ = { mutable desc : desc }
and desc =
  | T_unit
  | T_arrow  of typ * typ
  | T_forall of forall * typ
  | T_var    of { mutable forall : forall }
  | T_link   of typ
[@@deriving show { with_path = false }]

let current_level = ref 0
let enter_level () = incr current_level
let leave_level () = decr current_level
let current_level () = !current_level

let forall_stack = Stack.create ()
let enter_forall () =
  enter_level ();
  let level = current_level () in
  let forall_desc = Forall { generic = false; level } in
  let forall = { forall_desc } in
  Stack.push forall forall_stack

let leave_forall () =
  leave_level ();
  Stack.pop forall_stack
let current_forall () = Stack.top forall_stack

let rec forall_repr forall =
  match forall.forall_desc with
  | Forall _ -> forall
  | Forall_link forall -> forall_repr forall
let new_generic_forall () =
  { forall_desc = Forall { generic = true; level = -1 } }
let rec set_level forall level =
  match forall.forall_desc with
  | Forall desc -> desc.level <- level
  | Forall_link forall -> set_level forall level
let reset_generic_forall forall = set_level forall (-1)

let new_typ desc = { desc }
let new_var () =
  let forall = current_forall () in
  new_typ (T_var { forall })

let rec generalize forall body =
  match forall.forall_desc with
  | Forall desc ->
    desc.generic <- true;
    new_typ (T_forall (forall, body))
  | Forall_link forall -> generalize forall body

let rec weaken typ =
  match typ.desc with
  | T_link typ -> weaken typ
  | T_forall (forall, body) ->
    let current_forall = current_forall () in
    forall.forall_desc <- Forall_link current_forall;
    typ.desc <- T_link body
  | _ -> ()

let rec level forall =
  match forall.forall_desc with
  | Forall desc -> desc.level
  | Forall_link forall -> level forall
let rec is_generic forall =
  match forall.forall_desc with
  | Forall desc -> desc.generic
  | Forall_link forall -> is_generic forall
let is_weak forall = not (is_generic forall)

let rec copy foralls vars typ =
  let copy typ = copy foralls vars typ in
  match typ.desc with
  | T_link typ -> copy typ
  | T_unit -> typ
  | T_arrow (param, return) ->
    let param = copy param in
    let return = copy return in
    new_typ (T_arrow (param, return))
  | T_forall (forall, body) ->
    let forall = forall_repr forall in
    let forall =
      let forall' = new_generic_forall () in
      foralls := (forall, forall') :: !foralls;
      forall' in
    let body = copy body in
    new_typ (T_forall (forall, body))
  | T_var { forall } ->
    let forall = forall_repr forall in
    if is_generic forall then (
      match List.assq_opt typ !vars with
      | Some typ -> typ
      | None ->
        let forall = List.assq forall !foralls in
        let typ' = new_typ (T_var { forall }) in
        vars := (typ, typ') :: !vars;
        typ')
    else
      typ
let copy typ = copy (ref []) (ref []) typ

let instance typ =
  let typ = copy typ in
  weaken typ;
  typ

(* check for recursive bindings, update the levels *)
(* find smallest weak forall *)
let rec min_forall forall_ref typ =
  let min_forall typ = min_forall forall_ref typ in
  match typ.desc with
  | T_link typ -> min_forall typ
  | T_unit -> ()
  | T_arrow (param, return) ->
    min_forall param;
    min_forall return
  | T_forall (_forall, body) -> min_forall body
  | T_var { forall } ->
    let forall = forall_repr forall in
    if is_weak forall then
      if level forall < level !forall_ref then
        forall_ref := forall
let min_forall forall typ =
  let forall_ref = ref forall in
  min_forall forall_ref typ;
  !forall_ref

let rec update_forall forall typ =
  let update_forall typ = update_forall forall typ in
  match typ.desc with
  | T_link typ -> update_forall typ
  | T_unit -> ()
  | T_arrow (param, return) ->
    update_forall param;
    update_forall return
  | T_forall (_forall, body) -> update_forall body
  | T_var var ->
    if is_weak var.forall then
      var.forall <- forall

(* TODO: better name, root_var means the var being unified *)
let rec occurs root_var typ =
  let occurs typ = occurs root_var typ in
  match typ.desc with
  | T_link typ -> occurs typ
  | T_unit -> ()
  | T_arrow (param, return) ->
    occurs param;
    occurs return
  | T_forall (_forall, body) -> occurs body
  | T_var _var ->
    (* physical equality *)
    if root_var == typ then
      raise Occurs_check

let rec escapes min_level typ =
  let escapes typ = escapes min_level typ in
  match typ.desc with
  | T_link typ -> escapes typ
  | T_unit -> ()
  | T_arrow (param, return) ->
    escapes param;
    escapes return
  | T_forall (forall, body) ->
    reset_generic_forall forall;
    escapes body
  | T_var { forall } -> (
    match level forall with
    | -1 ->
      (* quantified by a forall inside of the var being unified *)
      ()
    | forall_level ->
      (* TODO: the level must be equal? *)
      if min_level <> forall_level then
        raise Escape_check)

(* TODO: is qvars needed? *)
let rec subtype ~expected ~received =
  (* physical identity *)
  if expected == received then
    ()
  else
    subtype_desc ~expected ~received

and subtype_desc ~expected ~received =
  match (expected.desc, received.desc) with
  | T_link expected, _ -> subtype ~expected ~received
  | _, T_link received -> subtype ~expected ~received
  | T_unit, T_unit -> ()
  | ( T_arrow (expected_param, expected_return),
      T_arrow (received_param, received_return) ) ->
    subtype ~expected:received_param ~received:expected_param;
    subtype ~expected:expected_return ~received:received_return
  | T_var _, _
  | _, T_var _ ->
    subtype_vars ~expected ~received
  | T_forall _, _
  | _, T_forall _ ->
    subtype_forall ~expected ~received
  | _ -> raise Type_clash

and subtype_vars ~expected ~received =
  let var, forall, typ =
    match (expected.desc, received.desc) with
    | T_var { forall = expected_forall }, T_var { forall = received_forall } ->
      if is_weak expected_forall then
        (expected, expected_forall, received)
      else
        (received, received_forall, expected)
    | T_var { forall }, _ -> (expected, forall, received)
    | _, T_var { forall } -> (received, forall, expected)
    | _ ->
      (* one must be a var and link is not reachable *)
      assert false in

  if is_generic forall then
    raise Escape_check;

  let forall = min_forall forall typ in
  update_forall forall typ;
  occurs var typ;
  escapes (level forall) typ;
  var.desc <- T_link typ

and subtype_forall ~expected ~received =
  match (expected.desc, received.desc) with
  | T_forall (expected_forall, expected_body), _ ->
    set_level expected_forall (current_level ());
    subtype_forall ~expected:expected_body ~received
  | _, T_forall _ ->
    weaken received;
    subtype_forall ~expected ~received
  | _, _ ->
    enter_level ();
    subtype ~expected ~received;
    leave_level ()

(* typer *)
let t_unit = new_typ T_unit
let rec transl env typ =
  match typ with
  | PT_unit -> t_unit
  | PT_arrow (param, return) ->
    let param = transl env param in
    let return = transl env return in
    new_typ (T_arrow (param, return))
  | PT_forall _ ->
    let forall = new_generic_forall () in
    let body = transl_forall env forall typ in
    new_typ (T_forall (forall, body))
  | PT_var var -> List.assoc var env

and transl_forall env forall typ =
  match typ with
  | PT_forall (var, body) ->
    let var_typ = new_typ (T_var { forall }) in
    let env = (var, var_typ) :: env in
    transl_forall env forall body
  | typ -> transl env typ

let transl typ = transl [] typ

let rec infer env expr =
  match expr with
  | PE_unit -> t_unit
  | PE_var var -> List.assoc var env
  | PE_let (var, value, body) ->
    let value_typ = infer env value in

    let env = (var, value_typ) :: env in
    infer env body
  | PE_lambda (param, param_typ, body) ->
    enter_forall ();
    let param_typ =
      match param_typ with
      | Some param_typ -> transl param_typ
      | None -> new_var () in
    let body_typ =
      let env = (param, param_typ) :: env in
      let body_typ = infer env body in
      instance body_typ in
    let typ = new_typ (T_arrow (param_typ, body_typ)) in
    let forall = leave_forall () in
    generalize forall typ
  | PE_apply (funct, arg) ->
    let funct_typ = instance (infer env funct) in

    enter_forall ();
    (* instance vs copy here, leads to different types on (choose id) *)
    let arg_typ = instance (infer env arg) in
    let return_typ = new_var () in
    let expected = new_typ (T_arrow (arg_typ, return_typ)) in
    subtype ~expected ~received:funct_typ;
    let forall = leave_forall () in
    generalize forall return_typ
