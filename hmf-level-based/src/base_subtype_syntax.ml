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
    | PT_unit -> PT_unit
    | PT_var name -> ( match find_opt name t with Some ty -> ty | None -> ty)
    | PT_arrow (param, return) -> PT_arrow (apply param t, apply return t)
    | PT_forall (name, ty) -> PT_forall (name, apply ty t)
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
module Context = struct
  module String_set = Set.Make (String)
  module String_map = Map.Make (String)
  type level = int
  type t = {
    level : level;
    expected : String_set.t;
    levels : level String_map.t;
  }
  let empty =
    { level = 0; expected = String_set.empty; levels = String_map.empty }
  let add_expected var t =
    let expected = String_set.add var t.expected in
    let levels = String_map.add var t.level t.levels in
    { t with expected; levels }

  let add_received var t =
    let levels = String_map.add var t.level t.levels in
    { t with levels }

  let is_expected var t = String_set.mem var t.expected
  let level var t = String_map.find_opt var t.levels
  let increment t = { t with level = t.level + 1 }
end
let rec subtype context ~expected ~received =
  let substs, ty = subtype' context ~expected ~received in
  (substs, ty)

and subtype' context ~expected ~received =
  match (expected, received) with
  | PT_unit, PT_unit -> (Subst.empty, PT_unit)
  | ( PT_arrow (expected_param, expected_return),
      PT_arrow (received_param, received_return) ) ->
      let substs_param, param =
        subtype context ~expected:received_param ~received:expected_param
      in
      let substs_return, return =
        let expected_return = Subst.apply expected_return substs_param in
        let received_return = Subst.apply received_return substs_param in
        subtype context ~expected:expected_return ~received:received_return
      in

      (Subst.merge substs_param substs_return, PT_arrow (param, return))
  | PT_var expected_var, PT_var received_var when expected_var = received_var ->
      (Subst.empty, expected)
  | PT_var expected_variable, PT_var received_variable ->
      let expected_level = Context.level expected_variable context in
      let received_level = Context.level received_variable context in
      if Context.is_expected expected_variable context then (
        if Context.is_expected received_variable context then
          error Constrained_forall;
        if expected_level > received_level then error Forall_escape;
        (Subst.singleton received_variable expected, expected))
      else (
        if received_level > expected_level then error Forall_escape;
        (Subst.singleton expected_variable received, received))
  | PT_var var, ty | ty, PT_var var ->
      if Context.is_expected var context then error Constrained_forall;
      (Subst.singleton var ty, ty)
  | PT_forall _, _ | _, PT_forall _ ->
      let context = Context.increment context in
      subtype_forall context ~expected ~received
  | _ -> error Type_clash

and subtype_forall context ~expected ~received =
  match (expected, received) with
  | PT_forall (expected_variable, expected_body), received ->
      let substs, body =
        let context = Context.add_expected expected_variable context in
        subtype_forall context ~expected:expected_body ~received
      in

      (substs, PT_forall (expected_variable, body))
  | expected, PT_forall (received_variable, received_body) ->
      let substs, body =
        let context = Context.add_received received_variable context in
        subtype context ~expected ~received:received_body
      in

      let substs = Subst.remove received_variable substs in
      (substs, body)
  | expected, received -> subtype context ~expected ~received

let rec closed context typ =
  match typ with
  | PT_unit -> ()
  | PT_var identifier ->
      if not (Context.is_expected identifier context) then error Open_type
  | PT_arrow (param, return) ->
      closed context param;
      closed context return
  | PT_forall (identifier, typ) ->
      let context = Context.add_expected identifier context in
      closed context typ
let closed typ = closed Context.empty typ
let rec rename typ =
  match typ with
  | PT_unit -> PT_unit
  | PT_var variable -> PT_var variable
  | PT_arrow (param, return) -> PT_arrow (rename param, rename return)
  | PT_forall (variable, body) ->
      let new_name = Unique_var.next () in
      let body =
        Subst.singleton variable (PT_var new_name) |> Subst.apply body
      in
      PT_forall (new_name, rename body)
let subtype ~expected ~received =
  closed expected;
  closed received;
  let expected = rename expected in
  let received = rename received in
  let substs, ty = subtype Context.empty ~expected ~received in
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
  let forall_a = Syntax.typ_from_string "forall a. a" |> Option.get
  let make_tests (supertype, subtype) =
    let supertype = Syntax.typ_from_string supertype |> Option.get in
    let subtype = Syntax.typ_from_string subtype |> Option.get in
    [
      Accepted { expected = supertype; received = subtype };
      Rejected { expected = subtype; received = supertype };
      Accepted { expected = supertype; received = supertype };
      Accepted { expected = subtype; received = subtype };
      Accepted { expected = subtype; received = forall_a };
      Accepted { expected = supertype; received = forall_a };
      Rejected { expected = forall_a; received = subtype };
      Rejected { expected = forall_a; received = supertype };
      Accepted
        {
          expected = PT_forall (Unique_var.next (), supertype);
          received = PT_forall (Unique_var.next (), subtype);
        };
      Rejected
        {
          expected = PT_forall (Unique_var.next (), subtype);
          received = PT_forall (Unique_var.next (), supertype);
        };
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
