module type S = sig
  type var = string
  type typ =
    | PT_unit
    | PT_arrow  of typ * typ
    | PT_var    of var
    | PT_forall of var * typ
  type expr =
    | PE_unit
    | PE_var    of var
    | PE_let    of var * expr * expr
    | PE_lambda of var * typ option * expr
    | PE_apply  of expr * expr
end
