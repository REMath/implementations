(* decode instruction given on command line *)

let () =
  let s = Array.fold_right
            (fun a acc ->
               try Camlcoq.Z.of_sint (int_of_string a) :: acc
               with _ -> acc)
            Sys.argv
            [] 
  in
  Printf.printf "%s\n" (
    match Goto.decode_instr s with
    | Some (i, _) -> Utils.string_of_instr i
    | None -> "⊥"
  )

