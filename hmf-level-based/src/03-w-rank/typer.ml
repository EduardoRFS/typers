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
and forall = level ref
and typ = { mutable desc : desc }
and desc =
  | T_unit
  | T_arrow  of typ * typ
  | T_forall of forall * typ
  | T_var    of var ref
  | T_link   of typ
and var =
  (* maybe be bound if wrapped by a forall *)
  | Unbound of level
  | Bound   of forall
[@@deriving show { with_path = false }]

let current_level = ref 0
let enter_level () = incr current_level
let leave_level () = decr current_level
let current_level () = !current_level

let new_typ desc = { desc }
let new_var () =
  let level = current_level () in
  let var = ref (Unbound level) in
  new_typ (T_var var)

let new_forall () = ref (-1)
let reset_forall forall = forall := -1

let rec generalize forall typ =
  let generalize typ = generalize forall typ in
  match typ.desc with
  | T_link typ -> generalize typ
  | T_unit -> ()
  | T_arrow (param, return) ->
    generalize param;
    generalize return
  | T_forall (_forall, body) -> generalize body
  | T_var ({ contents = Unbound level } as var) ->
    (* TODO: maybe level = current_level () ? *)
    if level > current_level () then
      var := Bound forall
    else
      ()
  | T_var { contents = Bound _forall } -> ()
let generalize body =
  let forall = new_forall () in
  generalize forall body;
  new_typ (T_forall (forall, body))

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
    let forall =
      let forall' = new_forall () in
      foralls := (forall, forall') :: !foralls;
      forall' in
    let body = copy body in
    new_typ (T_forall (forall, body))
  | T_var { contents = Unbound _level } -> typ
  | T_var ({ contents = Bound forall } as var) -> (
    (* physical identity *)
    match List.assq_opt var !vars with
    | Some typ -> typ
    | None ->
      let forall = List.assq forall !foralls in
      let typ = new_typ (T_var (ref (Bound forall))) in
      vars := (var, typ) :: !vars;
      typ)
let copy typ = copy (ref []) (ref []) typ

let rec weaken_body forall typ =
  let weaken_body typ = weaken_body forall typ in
  match typ.desc with
  | T_link typ -> weaken_body typ
  | T_unit -> ()
  | T_arrow (param, return) ->
    weaken_body param;
    weaken_body return
  | T_forall (_forall, body) -> weaken_body body
  | T_var { contents = Unbound _level } -> ()
  | T_var ({ contents = Bound forall' } as var) ->
    if forall == forall' then
      var := Unbound (current_level ())
let rec weaken typ =
  match typ.desc with
  | T_link typ -> weaken typ
  | T_forall (forall, body) ->
    weaken_body forall body;
    forall := current_level ();
    typ.desc <- T_link body
  | _ -> ()

let instance typ =
  let typ = copy typ in
  weaken typ;
  typ

(* check for recursive bindings, update the levels *)
let rec occurs var min_level typ =
  let occurs typ = occurs var min_level typ in
  match typ.desc with
  | T_link typ -> occurs typ
  | T_unit -> ()
  | T_arrow (param, return) ->
    occurs param;
    occurs return
  | T_forall (_forall, body) -> occurs body
  | T_var ({ contents = Unbound level } as var') ->
    (* physical equality *)
    if var == typ then
      raise Occurs_check;

    min_level := min !min_level level;
    var' := Unbound !min_level
  | T_var { contents = Bound _forall } -> ()
let occurs var level typ =
  let min_level = ref level in
  occurs var min_level typ;
  !min_level

let rec escapes level typ =
  let escapes typ = escapes level typ in
  match typ.desc with
  | T_link typ -> escapes typ
  | T_unit -> ()
  | T_arrow (param, return) ->
    escapes param;
    escapes return
  | T_forall (forall, body) ->
    reset_forall forall;
    escapes body
  | T_var { contents = Unbound _ } -> ()
  | T_var { contents = Bound forall } -> (
    match !forall with
    | -1 ->
      (* quantified by a forall inside of the var being unified *)
      ()
    | forall_level ->
      (* TODO: the level must be equal? *)
      if level <> forall_level then
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
  let var, level, typ =
    match (expected.desc, received.desc) with
    | T_var { contents = Unbound level }, _ -> (expected, level, received)
    | _, T_var { contents = Unbound level } -> (received, level, expected)
    | T_var { contents = Bound _ }, _
    | _, T_var { contents = Bound _ } ->
      raise Escape_check
    | _ ->
      (* one must be a var and link is not reachable *)
      assert false in

  let level = occurs var level typ in
  escapes level typ;
  var.desc <- T_link typ

and subtype_forall ~expected ~received =
  match (expected.desc, received.desc) with
  | T_forall (expected_forall, expected_body), _ ->
    expected_forall := current_level ();
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
    let forall = new_forall () in
    let body = transl_forall env forall typ in
    new_typ (T_forall (forall, body))
  | PT_var var -> List.assoc var env

and transl_forall env forall typ =
  match typ with
  | PT_forall (var, body) ->
    let var_typ = new_typ (T_var (ref (Bound forall))) in
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
    enter_level ();
    let param_typ =
      match param_typ with
      | Some param_typ -> transl param_typ
      | None -> new_var () in
    let body_typ =
      let env = (param, param_typ) :: env in
      let body_typ = infer env body in
      instance body_typ in
    let typ = new_typ (T_arrow (param_typ, body_typ)) in
    leave_level ();
    generalize typ
  | PE_apply (funct, arg) ->
    let funct_typ = instance (infer env funct) in

    enter_level ();
    (* instance vs copy here, leads to different types on (choose id) *)
    let arg_typ = instance (infer env arg) in
    let return_typ = new_var () in
    let expected = new_typ (T_arrow (arg_typ, return_typ)) in
    subtype ~expected ~received:funct_typ;
    leave_level ();

    generalize return_typ
