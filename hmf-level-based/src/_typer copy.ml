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

type forall = int
and level = int
and typ =
  | T_unit
  | T_arrow  of typ * typ
  | T_forall of forall * typ
  | T_var    of var ref
and var =
  (* maybe be bound if wrapped by a forall *)
  | Unbound    of level
  | Quantified of forall
  | Link       of typ
[@@deriving show { with_path = false }]

let last_id = ref 0
let next_id () =
  incr last_id;
  !last_id

let current_level = ref 0
let enter_level () = incr current_level
let leave_level () = decr current_level
let current_level () = !current_level

let next_var () =
  let var_id = next_id () in
  T_var var_id

let rec free_typ qvars typ =
  match typ with
  | T_unit -> []
  | T_arrow (param, return) -> free_typ qvars param @ free_typ qvars return
  | T_forall (var_id, body) -> free_typ (var_id :: qvars) body
  | T_var var_id -> if List.mem var_id qvars then [] else [var_id]
let free_typ typ =
  let vars = free_typ [] typ in
  List.sort_uniq Int.compare vars

let free_env env =
  let vars = List.concat_map (fun (_var_id, typ) -> free_typ typ) env in
  List.sort_uniq Int.compare vars

let is_free var_id typ = List.mem var_id (free_typ typ)

(* true if var_id appears in substs codomain *)
let is_free_in_codom var_id substs =
  List.exists (fun (_var_id, typ) -> is_free var_id typ) substs

let rec generalize forall typ =
  let generalize typ = generalize forall typ in
  match typ with
  | T_unit -> ()
  | T_arrow (param, return) ->
    generalize param;
    generalize return
  | T_forall (_forall, body) -> generalize body
  | T_var ({ contents = Unbound level } as var) ->
    (* TODO: maybe level = current_level () ? *)
    if level > current_level () then
      var := Quantified forall
    else
      ()
  | T_var { contents = Quantified _forall } -> ()
  | T_var { contents = Link typ } -> generalize typ

let rec copy foralls vars typ =
  let copy typ = copy foralls vars typ in
  match typ with
  | T_unit -> T_unit
  | T_arrow (param, return) ->
    let param = copy param in
    let return = copy return in
    T_arrow (param, return)
  | T_forall (forall, body) ->
    let forall =
      let forall' = next_id () in
      foralls := (forall, forall') :: !foralls;
      forall' in
    let body = copy body in
    T_forall (forall, body)
  | T_var { contents = Unbound _level } -> typ
  | T_var ({ contents = Quantified forall } as var) -> (
    (* physical identity *)
    match List.assq_opt var !vars with
    | Some typ -> typ
    | None ->
      let forall = List.assoc forall !foralls in
      let typ = T_var (ref (Quantified forall)) in
      vars := (var, typ) :: !vars;
      typ)
  | T_var { contents = Link typ } -> copy typ
let copy typ = copy (ref []) (ref []) typ

let rec weaken forall typ =
  let weaken typ = weaken forall typ in
  match typ with
  | T_unit -> ()
  | T_arrow (param, return) ->
    weaken param;
    weaken return
  | T_forall (_forall, body) -> weaken body
  | T_var { contents = Unbound _ } -> ()
  | T_var ({ contents = Quantified forall' } as var) ->
    if forall = forall' then
      var := Unbound (current_level ())
    else
      ()
  | T_var { contents = Link typ } -> weaken typ
let weaken typ =
  match typ with
  | T_forall (forall, body) -> weaken forall body
  | _ -> ()

let instance typ =
  let typ = copy typ in
  weaken typ;
  typ

let funmatch typ =
  match typ with
  | T_unit -> raise Type_clash
  | T_arrow (param, return) -> (param, return)
  | T_forall _ -> assert false
  | T_var (_var_id, var) ->
    let param = next_var () in
    let return = next_var () in
    let typ = T_arrow (param, return) in

    (* TODO: ideally this should not be here *)
    var := Link typ;
    (param, return)

(* check for recursive bindings, update the levels *)
let rec occurs var level typ =
  let occurs typ = occurs var level typ in
  match typ with
  | T_unit -> ()
  | T_arrow (param, return) ->
    occurs param;
    occurs return
  | T_forall (_forall, body) -> occurs body
  | T_var ({ contents = Unbound level' } as var') ->
    (* physical equality *)
    if var == var' then
      raise Occurs_check;

    let min_level = min level level' in
    var' := Unbound min_level
  | T_var { contents = Quantified _forall } -> ()
  | T_var { contents = Link typ } -> occurs typ

(* TODO: is qvars needed? *)
let rec subtype qvars ~expected ~received =
  (* physical identity *)
  if expected == received then
    ()
  else
    subtype_desc qvars ~expected ~received

and subtype_desc qvars ~expected ~received =
  match (expected, received) with
  | T_unit, T_unit -> ()
  | ( T_arrow (expected_param, expected_return),
      T_arrow (received_param, received_return) ) ->
    subtype qvars ~expected:received_param ~received:expected_param;
    subtype qvars ~expected:expected_return ~received:received_return
  | T_var { contents = Link expected }, received
  | expected, T_var { contents = Link received } ->
    (* TODO: is qvars needed? *)
    subtype qvars ~expected ~received
  | T_var _, _
  | _, T_var _ ->
    subtype_vars qvars ~expected ~received
  | T_forall _, _
  | _, T_forall _ ->
    subtype_forall qvars ~expected ~received
  | _ -> raise Type_clash

and subtype_vars qvars ~expected ~received =
  let var, level, typ =
    match (expected, received) with
    | ( T_var
          ( expected_var_id,
            ({ contents = Unbound expected_level } as expected_var) ),
        T_var
          ( received_var_id,
            ({ contents = Unbound received_level } as received_var) ) ) ->
      if List.mem expected_var_id qvars then (
        if List.mem received_var_id qvars then
          raise Escape_check;
        (received_var, received_level, expected))
      else
        (expected_var, expected_level, received)
    | T_var (_var_id, ({ contents = Unbound level } as var)), typ
    | typ, T_var (_var_id, ({ contents = Unbound level } as var)) ->
      (var, level, typ)
    | _ ->
      (* one must be a var and link is not reachable *)
      assert false in

  occurs var level typ;
  var := Link typ

and subtype_forall qvars ~expected ~received =
  match (expected, received) with
  | T_forall (expected_var_id, body), received ->
    let qvars = expected_var_id :: qvars in
    let substs = subtype_forall qvars ~expected:body ~received in
    if is_free_in_codom expected_var_id substs then
      raise Escape_check;
    substs
  | expected, T_forall (received_var_id, received_body) ->
    let substs = subtype_forall qvars ~expected ~received:received_body in
    let substs =
      List.filter (fun (var_id, _typ) -> var_id <> received_var_id) substs in
    substs
  | expected, received -> subtype qvars ~expected ~received
let subtype ~expected ~received = subtype [] ~expected ~received

let subsume ~expected ~received =
  (* TODO: this may be different from the paper *)
  let expected_vars, expected = instance expected in
  let received_vars, received = instance received in
  let substs = subtype ~expected ~received in

  (* remove received_vars *)
  let substs =
    List.filter
      (fun (var_id, _typ) -> not (List.mem var_id received_vars))
      substs in

  let expected_var_on_substs =
    List.exists
      (fun skolem_var -> is_free_in_codom skolem_var substs)
      expected_vars in
  if expected_var_on_substs then
    raise Escape_check;

  (* TODO: I think this checking may be missing on the paper, example:

     expected :: forall a. a  -> ()
     received ::           () -> ()
  *)
  let expected_var_bound =
    List.exists
      (fun skolem_var -> List.mem_assoc skolem_var substs)
      expected_vars in
  if expected_var_bound then
    raise Escape_check;

  substs

(* typer *)
let rec transl env typ =
  match typ with
  | PT_unit -> T_unit
  | PT_arrow (param, return) ->
    let param = transl env param in
    let return = transl env return in
    T_arrow (param, return)
  | PT_forall (var, body) ->
    let id = next_id () in
    let env = (var, id) :: env in
    let body = transl env body in
    T_forall (id, body)
  | PT_var var ->
    let id = List.assoc var env in
    T_var id
let transl typ = transl [] typ

let rec infer env expr =
  match expr with
  | PE_unit -> ([], T_unit)
  | PE_var var -> ([], List.assoc var env)
  | PE_let (var, value, body) ->
    let substs_1, value_typ = infer env value in
    let substs_2, body_typ =
      let env = subst_env substs_1 env in
      let env = (var, value_typ) :: env in
      infer env body in
    let substs = substs_2 @ substs_1 in
    (substs, body_typ)
  | PE_lambda (param, param_typ, body) ->
    let param_typ =
      match param_typ with
      | Some param_typ -> transl param_typ
      | None ->
        let var_id = next_id () in
        T_var var_id in

    let substs, body_typ =
      let env = (param, param_typ) :: env in
      let substs, body_typ = infer env body in
      let _vars, body_typ = instance body_typ in
      (substs, body_typ) in

    let env = subst_env substs env in
    let param_typ = subst_typ substs param_typ in
    let typ = T_arrow (param_typ, body_typ) in
    (substs, generalize env typ)
  | PE_apply (funct, arg) ->
    let substs_0, funct_typ = infer env funct in
    let substs_1, param_typ, return_typ =
      let _vars, funct_typ = instance funct_typ in
      funmatch funct_typ in
    let substs_2, arg_typ =
      let env = subst_env substs_0 env in
      let env = subst_env substs_1 env in
      infer env arg in
    let substs_3 =
      let param_typ = subst_typ substs_2 param_typ in
      subsume ~expected:param_typ ~received:arg_typ in
    (* TODO: is this way of merging substitutions correct *)
    let substs = substs_3 @ substs_2 @ substs_1 @ substs_0 in

    let env = subst_env substs env in
    let typ = subst_typ substs return_typ in
    (substs, generalize env typ)
