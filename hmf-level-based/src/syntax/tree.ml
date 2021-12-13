type ident = string [@@deriving show { with_path = false }]
type typ =
  | PT_unit
  | PT_arrow of typ * typ
  | PT_var of ident
  | PT_forall of ident * typ
[@@deriving show { with_path = false }]
let pp_raw_typ = pp_typ
let show_raw_typ = show_typ
let rec pp_typ fmt ty =
  let fprintf k = Format.fprintf fmt k in
  match ty with
  | PT_unit -> fprintf "()"
  | PT_arrow (((PT_arrow _ | PT_forall _) as param), return) ->
      fprintf "(%a) -> %a" pp_typ param pp_typ return
  | PT_arrow (param, return) -> fprintf "%a -> %a" pp_typ param pp_typ return
  | PT_var name -> fprintf "%s" name
  | PT_forall (name, ty) ->
      let rec collect_names acc ty =
        match ty with
        | PT_forall (name, ty) -> collect_names (name :: acc) ty
        | _ -> (acc, ty)
      in
      let names, ty = collect_names [ name ] ty in
      let names = String.concat " " names in
      fprintf "forall %s. %a" names pp_typ ty
let show_typ = Format.asprintf "%a" pp_typ
type pat = PP_unit | PP_ident of ident | PP_constraint of pat * typ
[@@deriving show { with_path = false }]
type expr =
  | PE_unit
  | PE_ident of ident
  | PE_arrow of pat * expr
  | PE_apply of expr * expr
  | PE_let of pat * expr * expr
  | PE_constraint of expr * typ
[@@deriving show { with_path = false }]
