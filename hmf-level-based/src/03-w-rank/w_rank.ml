open Typer
open Syntax.Make (Tree)

module Utils = struct
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

  let var_name context var =
    let next_id, names = context in
    match List.assq_opt var !names with
    | Some name -> name
    | None ->
      let id = !next_id in
      incr next_id;

      let name = to_string id in
      names := (var, name) :: !names;
      name

  let rec pp_typ context fmt typ =
    let pp_typ fmt typ = pp_typ context fmt typ in
    let printf s = Format.fprintf fmt s in

    match typ.desc with
    | T_link typ -> pp_typ fmt typ
    | T_unit -> printf "()"
    | T_arrow (param, return) ->
      let rec loop param =
        match param.desc with
        | T_link typ -> loop typ
        | T_arrow _
        | T_forall _ ->
          printf "(%a)" pp_typ param
        | _ -> printf "%a" pp_typ param in
      loop param;
      printf " -> %a" pp_typ return
    | T_forall (forall, body) -> (
      let rec loop typ =
        match typ.desc with
        | T_link typ -> loop typ
        | T_unit -> []
        | T_arrow (param, return) ->
          (* OCaml arg eval order is right-to-left *)
          let vars = loop param in
          vars @ loop return
        | T_forall (_forall, body) -> loop body
        | T_var { contents = Unbound _ } -> []
        | T_var ({ contents = Bound forall' } as var) ->
          if forall == forall' then
            let name = var_name context var in
            [name]
          else
            [] in
      let vars = List.sort_uniq String.compare (loop body) in
      match vars with
      | [] -> pp_typ fmt body
      | vars ->
        let vars = String.concat " " vars in
        printf "forall %s. %a" vars pp_typ body)
    | T_var ({ contents = Unbound _ } as var) ->
      printf "_%s" (var_name context var)
    | T_var ({ contents = Bound _ } as var) ->
      printf "%s" (var_name context var)
  let pp_typ fmt typ = pp_typ (ref 0, ref []) fmt typ
end

let print_typ code =
  let expr = expr_from_string code |> Option.get in
  enter_level ();
  let typ = infer [] expr in
  leave_level ();
  let typ = generalize typ in
  Format.printf "%a\n%!" Utils.pp_typ typ

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
