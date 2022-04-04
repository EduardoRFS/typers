open Typer
open Syntax.Make (Tree)

let () = Printexc.record_backtrace true

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
    let typ = repr typ in

    (if has_forall typ then
       let forall = level_ref typ.forall in
       let rec loop typ =
         let typ = repr typ in
         match typ.desc with
         | T_unit -> []
         | T_arrow (param, return) ->
           (* OCaml arg eval order is right-to-left *)
           let vars = loop param in
           vars @ loop return
         | T_var ->
           if level_ref typ.forall == forall then
             let name = var_name context typ in
             [name]
           else
             []
         | T_link _ -> assert false in
       let vars = List.sort_uniq String.compare (loop typ) in
       match vars with
       | [] -> ()
       | vars ->
         let vars = String.concat " " vars in
         printf "forall %s. " vars);

    match typ.desc with
    | T_unit -> printf "()"
    | T_arrow (param, return) ->
      let param = repr param in
      let is_arrow =
        match param.desc with
        | T_arrow _ -> true
        | _ -> false in
      if is_arrow || has_forall param then
        printf "(%a) -> %a" pp_typ param pp_typ return
      else
        printf "%a -> %a" pp_typ param pp_typ return
    | T_var ->
      if is_generic typ.forall then
        printf "%s" (var_name context typ)
      else
        printf "_%s" (var_name context typ)
    | T_link _ -> assert false
  let pp_typ fmt typ = pp_typ (ref 0, ref []) fmt typ
end

let print_typ code =
  let expr = expr_from_string code |> Option.get in
  let typ =
    with_forall @@ fun () ->
    let typ = infer [] expr in
    instance typ in
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

let () =
  print_typ
    {|
      let f =
        fun (funct: (forall a. (forall b. b -> b) -> a -> a) -> ()) ->
        fun arg ->
          funct arg in
      f
    |}
