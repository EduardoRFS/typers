module Level : sig
  type level [@@deriving show]
  type t = level

  val compare : t -> t -> int

  val is_generic : t -> bool
  val is_weak : t -> bool
  val generalize : t -> t
  val weaken : t -> t

  val mark : t -> t
  val unmark : t -> t
  val is_marked : t -> bool

  val initial : t
  val increment : t -> t
end = struct
  type t = int
  type level = int

  (* level : mark : weak  *)

  let compare = Int.compare

  let is_generic t = t land 0b1 == 0
  let is_weak t = t land 0b1 == 0b1

  let generalize t = t land -2
  let weaken t = t lor 0b1

  let mark t = t lor 0b10
  let unmark t = t land -3
  let is_marked t = t land 0b10 == 0b10

  let initial = weaken 0
  let increment t = t + 0b100

  let pp_level fmt level =
    if is_marked level then Format.fprintf fmt "!";
    if is_weak level then Format.fprintf fmt "_";
    Format.fprintf fmt "%d" (level lsr 2)
  let show_level = Format.asprintf "%a" pp_level
end

open Level

type 'a typ = {
  mutable level : 'a level_or_typ;
  mutable desc : desc;
}
and desc =
  | T_arrow of ex_typ * ex_typ
  | T_var
  | T_link  of ex_typ
and 'a level_or_typ
and ex_typ = Ex_typ : _ typ -> ex_typ [@@unboxed]
and typ_constructor = level typ
and typ_var = level typ typ

module Level_or_typ_constructor : sig
  type nonrec 'a level_or_typ = 'a level_or_typ
  type 'a t = 'a level_or_typ

  type 'a witness =
    | Level : level witness
    | Typ_constructor : level typ witness

  (* TODO: better name for this function *)
  val witness : 'a t -> 'a witness

  val of_level : level -> level t
  val to_level : level t -> level

  val of_typ_constructor : typ_constructor -> typ_constructor t
  val to_typ_constructor : typ_constructor t -> typ_constructor
end = struct
  type nonrec 'a level_or_typ = 'a level_or_typ
  type 'a t = 'a level_or_typ

  type 'a witness =
    | Level : level witness
    | Typ_constructor : level typ witness

  let witness (type a) (t : a t) : a witness =
    let obj = Obj.repr t in
    (* TODO: this can be made by using Obj.magic on Obj.is_int*)
    if Obj.is_int obj then
      let witness = Level in
      Obj.magic witness
    else
      let witness = Typ_constructor in
      Obj.magic witness

  let of_level (level : level) : level t = Obj.magic level
  let to_level (t : level t) : level = Obj.magic t

  let of_typ_constructor (typ : typ_constructor) : typ_constructor t =
    Obj.magic typ
  let to_typ_constructor (t : typ_constructor t) : typ_constructor = Obj.magic t
end
open Level_or_typ_constructor

let witness (type a) (typ : a typ) : a witness = witness typ.level

(* TODO: path compression*)
let rec repr ex_t =
  let (Ex_typ t) = ex_t in
  match t.desc with
  | T_link t -> repr t
  | _ -> ex_t

let desc typ =
  let (Ex_typ typ) = repr typ in
  typ.desc

(* TODO: explain this, in most cases it should be only used after repr typ *)
let level (Ex_typ typ) =
  match witness typ with
  | Level -> to_level typ.level
  | Typ_constructor ->
    let typ_constructor = to_typ_constructor typ.level in
    to_level typ_constructor.level

let has_forall (Ex_typ typ) =
  match witness typ with
  | Level -> true
  | Typ_constructor -> false

let is_generic typ = Level.is_generic (level typ)
let is_weak typ = Level.is_weak (level typ)

let weaken (typ : typ_constructor) =
  (* TODO: should ever only weaken generic *)
  let level = to_level typ.level in
  let level = weaken level in
  typ.level <- of_level level

type error =
  | Constrained_forall
  | Forall_escape
exception Error of error
let error error = raise (Error error)

let rec unify level ~expected ~received =
  (* TODO: if equal and repr *)
  let expected_is_weak = is_weak expected in
  let received_is_weak = is_weak received in

  if expected_is_weak || received_is_weak then
    let weak, other =
      if expected_is_weak then (expected, received) else (received, expected)
    in
    unify_desc level ~weak other
  else
    unify_forall level ~expected ~received

(* responsible for enforcing forall properties
   both types here should be generic *)
and unify_forall level ~expected ~received =
  let level = Level.increment level in

  let () =
    let (Ex_typ expected) = expected in
    match witness expected with
    | Level ->
      (* TODO: put this in a function *)
      expected.level <- of_level level
    | Typ_constructor -> () in

  let () =
    let (Ex_typ received) = received in
    match witness received with
    (* TODO: better name, but Level implies a forall is present *)
    | Level ->
      received.level <- of_level level;
      weaken received
    | Typ_constructor -> error Constrained_forall in

  unify_desc level ~weak:received expected

and unify_desc level ~weak other =
  match (desc weak, desc other) with
  | ( T_arrow (expected_param, expected_return),
      T_arrow (received_param, received_return) ) ->
    unify level ~expected:received_param ~received:expected_param;
    unify level ~expected:expected_return ~received:received_return
    (* TODO: T_link here *)
  | T_var, _
  | _, T_var ->
    ()

let make level desc = { level; desc }
let arrow level param return = make level (T_arrow (param, return))

(* SETUP -> EXECUTE -> VERIFY *)

let () = Random.self_init ()

type ident = string
type canonical_typ =
  | Arrow of canonical_typ * canonical_typ * ident list
  | Var   of ident

let arrow vars param return = Arrow (param, return, vars)
let var ident = Var ident

let unbounded_var = var
let new_var = var

type ident = string [@@deriving show { with_path = false }]
type typ =
  | PT_unit
  | PT_arrow  of typ * typ
  | PT_var    of ident
  | PT_forall of ident * typ
[@@deriving show { with_path = false }]
module String_set = Set.Make (String)
let unit = PT_unit
let arrow param return = PT_arrow (param, return)
let var ident = PT_var ident
let forall ident body = PT_forall (ident, body)

module Unique_ident : sig
  type t [@@deriving ord, show]

  val initial : t
  val next : t -> t

  val name : t -> string
end = struct
  type t = {
    id : int;
    name : string;
  }
  [@@deriving show]
  let compare a b = Int.compare a.id b.id

  (* TODO: I really don't like this function, but it works *)
  let rec to_ident acc int =
    let diff = int mod 26 in
    let char = Char.chr (97 + diff) in
    let acc = char :: acc in
    let next = int / 26 in
    if next > 0 then
      to_ident acc (next - 1)
    else
      String.of_seq (List.to_seq acc)
  let to_ident int = to_ident [] int

  let make id = { id; name = to_ident id }
  let initial = make 0
  let next t = make (t.id + 1)
  let name t = t.name
end
module Unique_ident_set = Set.Make (Unique_ident)

module Context = struct
  (* TODO: maybe this should be abstract? *)
  type t = {
    next_ident : Unique_ident.t;
    (* TODO: unbounded will always be small, so maybe different data structures? *)
    unbounded : Unique_ident_set.t;
    unbounded_names : String_set.t;
  }

  let random_var context =
    let { next_ident; unbounded; unbounded_names } = context in
    let ident = next_ident in
    let next_ident = Unique_ident.next ident in
    { next_ident; unbounded; unbounded_names }

  let new_var context =
    let { next_ident; unbounded; unbounded_names } = context in
    let ident = next_ident in
    let next_ident = Unique_ident.next ident in
    let unbounded = Unique_ident_set.add ident unbounded in

    let name = Unique_ident.name ident in
    let unbounded_names = String_set.add name unbounded_names in
    ({ next_ident; unbounded; unbounded_names }, ident)

  let bound_var context ident =
    let { next_ident; unbounded; unbounded_names } = context in
    let unbounded = Unique_ident_set.remove ident unbounded in

    let name = Unique_ident.name ident in
    let unbounded_names = String_set.remove name unbounded_names in
    { next_ident; unbounded; unbounded_names }

  let is_bounded context name = String_set.mem name context.unbounded_names
end
module Seed = struct
  open Context
  let seed context =
    let unit = (context, unit) in
    let new_var =
      let context, ident = new_var context in
      let name = Unique_ident.name ident in
      (context, var name) in

    let unbounded_var =
      String_set.fold
        (fun name cases -> (context, var name) :: cases)
        context.unbounded_names [] in
    (* TODO: the following pattern could be removed by putting it on the fold initial accumulator*)
    [unit; new_var] @ unbounded_var
end
module Constructor = struct
  type 'a ty =
    | Base_type : Syntax.typ ty
    | Additional_type : Syntax.typ ty
    | Random_var : ident ty
    | Bound_var : ident ty
  type 'a args =
    | Call : 'a ty -> ('a -> Syntax.typ) args
    | Cons : 'a ty * 'b args -> ('a -> 'b) args
end
(*
forall a. a -> forall b. b -> b

forall a. a -> forall b. b -> b
*)

type 'a constructor_ty =
  | Base_type : Syntax.typ constructor_ty
  | Additional_type : Syntax.typ constructor_ty
  | Random_var : ident constructor_ty
  | Bound_var : ident constructor_ty
type 'a constructor_args =
  | Call : 'a constructor_ty -> ('a -> Syntax.typ) constructor_args
  | Cons :
      'a constructor_ty * 'b constructor_args
      -> ('a -> 'b) constructor_args

(* bases *)
(* TODO:
   this generates duplicated types

   forall a. forall b. a -> b
   forall a. forall b. b -> a
*)
(* TODO: also need to test duplicated ident forall a. a -> forall a. a -> a *)
let unbounded_var ident = var ident
let new_var ident = var ident

(*
generate true: a
generate true: _ -> a
generate false: a -> _

generate true: () -> a
generate true: (a -> ()) -> () -> a
*)

let depth = 32

module Add_nat_properties = struct
  let add a b = a + b

  let base = (0, 0)
  let next (a, b) =
    if a = b then
      (a + 1, 0)
    else
      (a, b + 1)

  let test (a, b) execute verify =
    let a_b = execute (a, b) in
    verify a_b (a, b);
    let b_a = execute (b, a) in
    verify b_a (b, a);
    assert (a_b = b_a)

  let rec run depth case execute verify =
    let depth = depth - 1 in
    test case execute verify;
    if depth = 0 then
      ()
    else
      let case = next case in
      run depth case execute verify

  let run depth execute verify = run depth base execute verify

  let counter = ref 0
  let execute (a, b) =
    incr counter;
    let output = add a b in
    Format.printf "add %d %d = %d\n%!" a b output;
    output

  let verify output (a, b) =
    if a = 0 then
      assert (output = b)
    else if b = 0 then
      assert (output = a)
    else (
      assert (output > a);
      assert (output > b))

  let () = run depth execute verify

  let () = Format.printf "add: %d\n%!" !counter
end

module Sum_tree_properties = struct
  let nat () = Random.int 4

  type tree =
    | Leaf of int
    | Node of tree * tree
  [@@deriving show { with_path = false }]

  let rec sum tree =
    match tree with
    | Leaf n -> n
    | Node (left, right) -> sum left + sum right

  let base n = Leaf n
  let node_left n case = Node (case, base n)
  let node_right n case = Node (base n, case)

  let test ~expected input execute verify =
    let output = execute input in
    verify ~expected ~output ~input

  let rec run acc depth case execute verify =
    let depth = depth - 1 in
    test ~expected:acc case execute verify;
    if depth = 0 then
      ()
    else
      let acc_left, case_left =
        let n = nat () in
        let acc = acc + n in
        let case = node_left n case in
        (acc, case) in
      let acc_right, case_right =
        let n = nat () in
        let acc = acc + n in
        let case = node_right n case in
        (acc, case) in
      run acc_left depth case_left execute verify;
      run acc_right depth case_right execute verify
  let run depth execute verify =
    let n = nat () in
    run n depth (base n) execute verify

  let counter = ref 0
  let execute input =
    incr counter;
    sum input
  let verify ~expected ~output ~input:_ = assert (expected = output)

  let () = run 8 execute verify

  let () = Format.printf "sum: %d\n%!" !counter
end
