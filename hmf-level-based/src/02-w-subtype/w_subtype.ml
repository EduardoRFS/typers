open Typer
open Syntax.Make (Tree)

let print_typ code =
  let expr = expr_from_string code |> Option.get in
  let _substs, typ = infer [] expr in
  Format.printf "%a\n%!" pp_typ typ

let () =
  print_typ
    {|
let id = fun x -> x in
let sequence = fun x -> id in
let call_id = fun (id: forall a. a -> a) ->
  sequence (id ()) id in
call_id id
|}
let () =
  print_typ
    {|
  let id = fun x -> x in
  let make_choose = fun (choose: forall a. a -> a -> a) -> choose in
  let choose = make_choose (fun x -> fun y -> y) in
  choose id
|}
(*requires deep instantiation *)

let () =
  print_typ
    {|
let f =
  fun (funct: (((() -> ()) -> ()) -> ()) -> ()) ->
  fun (arg:((forall a. a -> a) -> ()) -> ()) ->
    funct arg in
f
|}
