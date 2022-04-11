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

(* type machinery *)
module Id : sig
  type t
  val next : unit -> t
end = struct
  type t = int

  let next = ref 0
  let next () =
    let id = !next in
    next := id + 1;
    id
end
type typ =
  | T_arrow  of typ * typ
  | T_forall of {
      forall : Id.t;
      body : typ;
    }
  | T_var    of var
and var =
  | Weak  of { id : Id.t }
  | Bound of {
      id : Id.t;
      forall : Id.t;
    }

let var_id var =
  match var with
  | Weak { id } -> id
  | Bound { id; forall = _ } -> id
let same a b = var_id a = var_id b

let new_weak_var () =
  let id = Id.next () in
  Weak { id }

let is_in_vars ~var vars = List.exists (fun var' -> same var var') vars

let rec subst_var ~var ~to_ typ =
  let subst_var typ = subst_var ~var ~to_ typ in
  match typ with
  | T_var var' ->
    if same var var' then
      to_
    else
      typ
  | T_forall { forall; body } ->
    let body = subst_var body in
    T_forall { forall; body }
  | T_arrow (param, return) ->
    let param = subst_var param in
    let return = subst_var return in
    T_arrow (param, return)
let apply_substs substs typ =
  List.fold_left (fun typ (var, to_) -> subst_var ~var ~to_ typ) typ substs
let merge_substs ~base ~in_ =
  let base =
    List.map
      (fun (var, to_) ->
        let to_ = apply_substs in_ to_ in
        (var, to_))
      base in
  base @ in_

let rec is_in_typ ~var typ =
  let is_in_typ typ = is_in_typ ~var typ in
  match typ with
  | T_var var' -> same var var'
  | T_forall { forall = _; body } -> is_in_typ body
  | T_arrow (param, return) -> is_in_typ param || is_in_typ return

let occur_check ~var typ =
  (* TODO: proper exception *)
  if is_in_typ ~var typ then
    failwith "occur_check"

let remove_vars vars substs =
  List.filter (fun (var, _) -> not (is_in_vars ~var vars)) substs

let rec forall_vars ~forall vars typ =
  let forall_vars vars typ = forall_vars ~forall vars typ in
  match typ with
  | T_var (Weak _) -> vars
  | T_var (Bound { forall = var_forall; id = _ } as var) ->
    if var_forall = forall && not (is_in_vars ~var vars) then
      var :: vars
    else
      vars
  | T_forall { forall = _; body } -> forall_vars vars body
  | T_arrow (param, return) ->
    let vars = forall_vars vars param in
    forall_vars vars return
let forall_vars ~forall typ = forall_vars ~forall [] typ

let weaken ~forall typ =
  (* TODO: ugly function*)
  let vars = forall_vars ~forall typ in
  let vars_map = List.map (fun var -> (var, new_weak_var ())) vars in
  let weak_vars = List.map (fun (_var, weak_var) -> weak_var) vars_map in

  let substs =
    List.map (fun (var, weak_var) -> (var, T_var weak_var)) vars_map in
  let typ = apply_substs substs typ in
  (typ, weak_vars)

let is_in_codom ~var substs =
  List.exists (fun (_var, typ) -> is_in_typ ~var typ) substs
let escape_check ~vars substs =
  List.iter
    (fun var ->
      (* TODO: proper exception *)
      if is_in_codom ~var substs then
        failwith "escape check")
    vars

let rec unify ~expected ~received =
  match (expected, received) with
  (* 1: same var  *)
  | T_var expected, T_var received when same expected received -> []
  (* 2: weak vars *)
  | T_var (Weak _ as var), typ
  | typ, T_var (Weak _ as var) ->
    occur_check ~var typ;
    [(var, typ)]
  (* 3: expected forall *)
  | T_forall { forall; body }, received ->
    (* TODO: maybe body would need to be copied? *)
    let substs = unify ~expected:body ~received in
    let vars = forall_vars ~forall body in
    escape_check ~vars substs;
    substs
  (* 4: received forall *)
  | expected, T_forall { forall; body } ->
    let body, weak_vars = weaken ~forall body in
    let substs = unify ~expected ~received:body in
    remove_vars weak_vars substs
  (* bound vars *)
  | T_var (Bound _), _
  | _, T_var (Bound _) ->
    failwith "constrained forall"
  (* simple *)
  | ( T_arrow (expected_param, expected_return),
      T_arrow (received_param, received_return) ) ->
    let substs_param = unify ~expected:received_param ~received:expected_param in
    let substs_return =
      let expected_return = apply_substs substs_param expected_return in
      let received_return = apply_substs substs_param received_return in
      unify ~expected:expected_return ~received:received_return in
    merge_substs ~base:substs_param ~in_:substs_return

(* examples *)
let rec to_string acc int =
  let diff = int mod 26 in
  let char = Char.chr (97 + diff) in
  let acc = char :: acc in
  let next = int / 26 in
  if next > 0 then
    to_string acc (next - 1)
  else
    String.of_seq (List.to_seq acc)
let to_string int = to_string [] int

let rec pp_typ next_name vars fmt typ =
  let pp_typ fmt typ = pp_typ next_name vars fmt typ in
  let fprintf s = Format.fprintf fmt s in
  let name var =
    let var_id = var_id var in
    match List.assoc_opt var_id !vars with
    | Some name -> name
    | None ->
      let id = !next_name in
      let name = to_string id in

      next_name := id + 1;
      vars := (var_id, name) :: !vars;
      name in

  match typ with
  | T_var (Weak _ as var) -> fprintf "_%s" (name var)
  | T_var (Bound _ as var) -> fprintf "%s" (name var)
  | T_forall { forall; body } ->
    let vars = forall_vars ~forall body in
    let vars = List.rev vars in
    let vars = List.map name vars |> String.concat " " in
    fprintf "forall %s. %a" vars pp_typ body
  | T_arrow (param, return) ->
    let parens =
      match param with
      | T_var _ -> false
      | T_forall _
      | T_arrow _ ->
        true in
    if parens then
      fprintf "(%a) -> %a" pp_typ param pp_typ return
    else
      fprintf "%a -> %a" pp_typ param pp_typ return

let pp_typ fmt typ = pp_typ (ref 0) (ref []) fmt typ

let weak () =
  let id = Id.next () in
  T_var (Weak { id })
let var forall =
  let id = Id.next () in
  T_var (Bound { forall; id })
let forall f =
  let forall = Id.next () in
  let body = f forall in
  T_forall { forall; body }
let arrow param return = T_arrow (param, return)
let ( @=> ) = arrow

let typ_apply ~funct ~arg =
  let ret = weak () in
  let expected = arg @=> ret in
  let received = funct in
  let substs = unify ~expected ~received in
  apply_substs substs ret
let typ_unify typ ~received =
  let substs = unify ~expected:typ ~received in
  apply_substs substs typ

let id =
  forall @@ fun forall ->
  let a = var forall in
  a @=> a

let apply =
  forall @@ fun forall ->
  let a = var forall in
  let b = var forall in
  (a @=> b) @=> a @=> b

let sequence =
  forall @@ fun forall ->
  let a = var forall in
  a @=> id

let sequence_id = typ_apply ~funct:sequence ~arg:id
let sequence' =
  forall @@ fun forall ->
  let a = var forall in
  let b = var forall in
  a @=> b @=> b
let sequence'_id = typ_apply ~funct:sequence' ~arg:id

let choose =
  forall @@ fun forall ->
  let a = var forall in
  a @=> a @=> a

let choose_id = typ_apply ~funct:choose ~arg:id
let choose_id_id = typ_apply ~funct:choose_id ~arg:id

let id_inst = typ_unify choose_id ~received:id

(* ensures that received instantiates *)
let duplicated_graph =
  let a = weak () in
  let typ = a @=> a @=> a in
  let choose = id @=> id @=> id in
  typ_unify typ ~received:choose

let () = Format.printf "id: %a\n%!" pp_typ id
let () = Format.printf "apply: %a\n%!" pp_typ apply
let () = Format.printf "sequence: %a\n%!" pp_typ sequence
let () = Format.printf "sequence id: %a\n%!" pp_typ sequence_id
let () = Format.printf "sequence': %a\n%!" pp_typ sequence
let () = Format.printf "sequence' id: %a\n%!" pp_typ sequence'_id
let () = Format.printf "choose: %a\n%!" pp_typ choose
let () = Format.printf "choose id: %a\n%!" pp_typ choose_id
let () = Format.printf "choose id id: %a\n%!" pp_typ choose_id_id
let () = Format.printf "(choose id : id): %a\n%!" pp_typ id_inst
let () = Format.printf "duplicated_graph: %a\n%!" pp_typ duplicated_graph

(* TODO: test where type will appears twice *)
