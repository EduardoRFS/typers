open Syntax
module Unique_var : sig
  val next : unit -> string
end = struct
  (* TODO: I really don't like this function, but it works *)
  let rec to_string acc int =
    let diff = int mod 26 in
    let char = Char.chr (97 + diff) in
    let acc = char :: acc in
    let next = int / 26 in
    if next > 0 then to_string acc (next - 1)
    else String.of_seq (List.to_seq acc)

  let to_string int = to_string [] int
  let acc = ref (-1)
  let next () =
    incr acc;
    to_string !acc
end

type level = int [@@deriving show { with_path = false }]
type typ =
  | T_unit
  | T_arrow of typ * typ
  | T_var of ident * level * bool
  | T_forall of typ * level
[@@deriving show { with_path = false }]
let pp_raw_typ = pp_typ
let show_raw_typ = show_typ
let rec pp_typ fmt ty =
  let fprintf k = Format.fprintf fmt k in
  match ty with
  | T_unit -> fprintf "()"
  | T_arrow (((T_arrow _ | T_forall _) as param), return) ->
      fprintf "(%a) -> %a" pp_typ param pp_typ return
  | T_arrow (param, return) -> fprintf "%a -> %a" pp_typ param pp_typ return
  | T_var (name, level, weak) ->
      if weak then fprintf "_%s[%d]" name level else fprintf "%s[%d]" name level
  | T_forall (ty, level) ->
      let names = ref [] in
      let rec collect_names ty =
        match ty with
        | T_unit -> ()
        | T_arrow (param, return) ->
            collect_names param;
            collect_names return
        | T_var (name, var_level, _) when level = var_level ->
            names := name :: !names
        | T_var _ -> ()
        | T_forall (ty, _) -> collect_names ty
      in
      collect_names ty;
      let names = List.sort_uniq String.compare !names |> String.concat " " in
      fprintf "forall %s. %a" names pp_typ ty
let show_typ = Format.asprintf "%a" pp_typ
type type_errors =
  | Open_type
  | Constrained_forall
  | Forall_escape
  | Type_clash
  | Trying_to_substitute_same_variable_twice
[@@deriving show]
exception Type_error of type_errors
let error error = raise (Type_error error)
module Subst = struct
  include Map.Make (String)
  let add name ty t =
    if mem name t then error Trying_to_substitute_same_variable_twice
    else add name ty t
  let rec apply ty t =
    match ty with
    | T_unit -> T_unit
    | T_var (name, _level, _weak) -> (
        match find_opt name t with Some ty -> ty | None -> ty)
    | T_arrow (param, return) -> T_arrow (apply param t, apply return t)
    | T_forall (ty, level) -> T_forall (apply ty t, level)
  let merge left right =
    merge
      (fun _ left right ->
        match (left, right) with
        | Some a, None | None, Some a -> Some a
        | Some _, Some _ | None, None -> failwith "unreachable")
      left right

  let pp fmt t =
    let open Format in
    let fprintf t = fprintf fmt t in
    fprintf "{";
    bindings t
    |> List.map (fun (var, ty) -> asprintf "%s:%a" var pp_typ ty)
    |> String.concat "," |> fprintf "%s";
    fprintf "}"
end

module String_set = Set.Make (String)
module String_map = Map.Make (String)
module Context = struct
  type t = { level : level; expected : String_set.t }
  let empty = { level = 0; expected = String_set.empty }
  let add_expected var t =
    let expected = String_set.add var t.expected in
    { t with expected }

  let is_expected var t = String_set.mem var t.expected
  let level t = t.level
  let increment t = { t with level = t.level + 1 }
end

let rec transl_typ vars context ptyp =
  let context = Context.increment context in
  let transl_typ vars ptyp = transl_typ vars context ptyp in
  match ptyp with
  | PT_unit -> T_unit
  | PT_arrow (param, return) ->
      T_arrow (transl_typ vars param, transl_typ vars return)
  | PT_var ident -> (
      match String_map.find_opt ident vars with
      | Some ty -> ty
      | None -> error Open_type)
  | PT_forall _ -> transl_typ_forall vars context ptyp

and transl_typ_forall vars context ptyp =
  let level = Context.level context in
  match ptyp with
  | PT_forall (ident, body) ->
      let var = T_var (ident, level, false) in
      let vars = String_map.add ident var vars in
      transl_typ_forall vars context body
  | ptyp -> T_forall (transl_typ vars context ptyp, level)

let transl_typ context ptyp = transl_typ String_map.empty context ptyp

let rec weaken level ty =
  let weaken ty = weaken level ty in
  match ty with
  | T_unit -> T_unit
  | T_arrow (param, return) -> T_arrow (weaken param, weaken return)
  | T_var (name, var_level, _weak) when level = var_level ->
      T_var (name, level, true)
  | T_var _ -> ty
  | T_forall (body, level) -> T_forall (weaken body, level)
let rec subtype ~expected ~received =
  let substs, ty = subtype' ~expected ~received in
  (substs, ty)

and subtype' ~expected ~received =
  match (expected, received) with
  | T_unit, T_unit -> (Subst.empty, T_unit)
  | ( T_arrow (expected_param, expected_return),
      T_arrow (received_param, received_return) ) ->
      let substs_param, param =
        subtype ~expected:received_param ~received:expected_param
      in
      let substs_return, return =
        let expected_return = Subst.apply expected_return substs_param in
        let received_return = Subst.apply received_return substs_param in
        subtype ~expected:expected_return ~received:received_return
      in

      (Subst.merge substs_param substs_return, T_arrow (param, return))
  | T_var (expected_var, _, _), T_var (received_var, _, _)
    when expected_var = received_var ->
      (Subst.empty, expected)
  | ( T_var (expected_variable, expected_level, expected_weak),
      T_var (received_variable, received_level, received_weak) ) ->
      if not expected_weak then (
        if not received_weak then error Constrained_forall;
        if expected_level > received_level then error Forall_escape;
        (Subst.singleton received_variable expected, expected))
      else (
        if received_level > expected_level then error Forall_escape;
        (Subst.singleton expected_variable received, received))
  | T_var (var, _level, weak), ty | ty, T_var (var, _level, weak) ->
      if not weak then error Constrained_forall;
      (Subst.singleton var ty, ty)
  | T_forall _, _ | _, T_forall _ -> subtype_forall ~expected ~received
  | _ -> error Type_clash

and subtype_forall ~expected ~received =
  match (expected, received) with
  | T_forall (expected_body, expected_level), received ->
      let substs, body = subtype_forall ~expected:expected_body ~received in

      (substs, T_forall (body, expected_level))
  | expected, T_forall (received_body, received_level) ->
      let weakend_body = weaken received_level received_body in
      subtype ~expected ~received:weakend_body
  | expected, received -> subtype ~expected ~received

let rec rename vars typ =
  let rename typ = rename vars typ in
  match typ with
  | T_unit -> T_unit
  | T_var (variable, level, weak) -> (
      match String_map.find_opt variable !vars with
      | Some ty -> ty
      | None ->
          let new_name = Unique_var.next () in
          let ty = T_var (new_name, level, weak) in
          vars := String_map.add variable ty !vars;
          ty)
  | T_arrow (param, return) -> T_arrow (rename param, rename return)
  | T_forall (body, level) -> T_forall (rename body, level)
let rename typ = rename (ref String_map.empty) typ
let subtype ~expected ~received =
  let expected = rename expected in
  let received = rename received in
  let substs, ty = subtype ~expected ~received in
  (substs, ty)
type test =
  | Accepted of { expected : typ; received : typ }
  | Rejected of { expected : typ; received : typ }
[@@deriving show { with_path = false }]
let subtyping_tests =
  [
    ("() -> ()", "forall a. a -> a");
    ("() -> ()", "() -> forall a. a");
    ("() -> ()", "forall a. () -> a");
    ("(forall a. a) -> (forall a. a)", "forall a. a -> a");
    ("forall a. a -> a -> a", "forall a b. a -> b -> b");
    ("forall a. () -> a -> a", "() -> forall a. a -> a");
    ("forall a b. a -> b -> b", "forall a. a -> forall b. b -> b");
    ("(forall b. b) -> ()", "forall a. a -> ()");
  ]
module Test_engine = struct
  Printexc.record_backtrace true

  let forall_a =
    Syntax.typ_from_string "forall a. a"
    |> Option.get |> transl_typ Context.empty
  let make_tests (supertype, subtype) =
    let supertype =
      Syntax.typ_from_string supertype |> Option.get |> transl_typ Context.empty
    in
    let subtype =
      Syntax.typ_from_string subtype |> Option.get |> transl_typ Context.empty
    in
    [
      Accepted { expected = supertype; received = subtype };
      Rejected { expected = subtype; received = supertype };
      Accepted { expected = supertype; received = supertype };
      Accepted { expected = subtype; received = subtype };
      Accepted { expected = subtype; received = forall_a };
      Accepted { expected = supertype; received = forall_a };
      Rejected { expected = forall_a; received = subtype };
      Rejected { expected = forall_a; received = supertype };
    ]

  let debug = ref true
  let run_test test =
    let failed () =
      Format.asprintf "something wrong at %a" pp_test test |> failwith
    in
    match test with
    | Accepted { expected; received } -> (
        try
          let _ = subtype ~expected ~received in
          ()
        with Type_error error ->
          Format.asprintf "error \"%a\" at %a" pp_type_errors error pp_test test
          |> failwith)
    | Rejected { expected; received } -> (
        try
          let _ = subtype ~expected ~received in
          failed ()
        with Type_error _ -> ())

  let () = List.concat_map make_tests subtyping_tests |> List.iter run_test
end
