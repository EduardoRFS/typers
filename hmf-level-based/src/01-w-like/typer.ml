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

type id = int
and typ =
  | T_unit
  | T_arrow  of typ * typ
  | T_forall of id * typ
  | T_var    of id
[@@deriving show { with_path = false }]

let last_id = ref 0
let next_id () =
  incr last_id;
  !last_id
let next_var () =
  let var_id = next_id () in
  T_var var_id

let rec subst_typ substs typ =
  let subst_typ typ = subst_typ substs typ in
  match typ with
  | T_unit -> T_unit
  | T_arrow (param, return) -> T_arrow (subst_typ param, subst_typ return)
  | T_forall (id, body) -> T_forall (id, subst_typ body)
  | T_var id -> (
    match List.assoc_opt id substs with
    | Some typ -> typ
    | None -> T_var id)

let subst_env substs env =
  List.map (fun (var_id, typ) -> (var_id, subst_typ substs typ)) env

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

let rec split_forall acc typ =
  match typ with
  | T_forall (var_id, body) -> split_forall (var_id :: acc) body
  | typ -> (acc, typ)
let split_forall typ = split_forall [] typ

let generalize env typ =
  let free_in_typ = free_typ typ in
  let free_in_env = free_env env in
  let vars =
    List.filter (fun var_id -> not (List.mem var_id free_in_env)) free_in_typ
  in
  List.fold_left (fun typ var_id -> T_forall (var_id, typ)) typ vars

let instance typ =
  let vars, typ = split_forall typ in
  let vars, substs =
    vars
    |> List.map (fun var_id ->
           let var_id' = next_id () in
           let subst = (var_id, T_var var_id') in
           (var_id', subst))
    |> List.split in

  let typ = subst_typ substs typ in
  (vars, typ)

let funmatch typ =
  match typ with
  | T_unit -> raise Type_clash
  | T_arrow (param, return) -> ([], param, return)
  | T_forall _ -> assert false
  | T_var var_id ->
    let param = next_var () in
    let return = next_var () in
    let typ = T_arrow (param, return) in
    ([(var_id, typ)], param, return)

let rec unify ~expected ~received =
  match (expected, received) with
  | T_unit, T_unit -> []
  | ( T_arrow (expected_param, expected_return),
      T_arrow (received_param, received_return) ) ->
    let substs_param = unify ~expected:received_param ~received:expected_param in
    let substs_return =
      let expected_return = subst_typ substs_param expected_return in
      let received_return = subst_typ substs_param received_return in
      unify ~expected:expected_return ~received:received_return in
    substs_return @ substs_param
  | T_var expected_id, T_var received_id when expected_id = received_id -> []
  | T_var var_id, typ
  | typ, T_var var_id ->
    if is_free var_id typ then
      raise Occurs_check;
    [(var_id, typ)]
  | T_forall (expected_id, expected_body), T_forall (received_id, received_body)
    ->
    let temp_var_id = next_id () in
    let substs =
      let temp_var = T_var temp_var_id in
      let expected_body = subst_typ [(expected_id, temp_var)] expected_body in
      let received_body = subst_typ [(received_id, temp_var)] received_body in
      unify ~expected:expected_body ~received:received_body in
    if is_free_in_codom temp_var_id substs then
      raise Escape_check;
    substs
  | _ -> raise Type_clash

let subsume ~expected ~received =
  (* TODO: this may be different from the paper *)
  let expected_vars, expected = instance expected in
  let received_vars, received = instance received in
  let substs = unify ~expected ~received in

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

    (* TODO: why polymorphic check is needed? *)
    (substs, generalize env typ)
