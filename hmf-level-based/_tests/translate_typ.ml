open Syntax
open Utils
open Types

module Context : sig
  type t

  val make : unit -> t

  val make_unit : t -> forall -> typ
  val make_var : t -> forall -> typ
  val make_arrow : t -> forall -> param:typ -> return:typ -> typ

  val append_typ_var : ident -> typ -> t -> t
  val find_typ_var : ident -> t -> typ option
end = struct
  type t = {
    uid : Uid.t ref;
    typ_vars : typ String_map.t;
  }

  let make () = { uid = ref Uid.initial; typ_vars = String_map.empty }
  let new_uid t =
    let next_uid = !(t.uid) in
    t.uid := Uid.next next_uid;
    next_uid

  let make_unit t forall = make_unit forall (new_uid t)
  let make_var t forall = make_var forall (new_uid t)
  let make_arrow t forall ~param ~return =
    make_arrow forall (new_uid t) ~param ~return

  let append_typ_var name typ t =
    let { uid; typ_vars } = t in
    let typ_vars = String_map.add name typ typ_vars in
    { uid; typ_vars }
  let find_typ_var name t = String_map.find_opt name t.typ_vars
end

exception Unbound_type_variable of ident

let rec translate_typ context forall typ =
  let open Context in
  match typ with
  | PT_unit -> make_unit context forall
  | PT_var name -> (
    match find_typ_var name context with
    | Some typ -> typ
    | None -> raise (Unbound_type_variable name))
  | PT_arrow (param, return) ->
    let param = translate_typ context forall param in
    let return = translate_typ context forall return in
    make_arrow context forall ~param ~return
  | PT_forall (name, body) ->
    let var = make_var context forall in
    let context = append_typ_var name var context in
    translate_typ context forall body

let translate_typ typ =
  let context = Context.make () in
  translate_typ context (ref Level.initial) typ
