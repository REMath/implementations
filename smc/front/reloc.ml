open Goto

let reloc
      (getlabel: string -> int)
      (prog: (((string -> Camlcoq.Z.t) -> instruction) * bool) list)
      : instruction list =
  let offsets : (int, int) Hashtbl.t = Hashtbl.create 17 in
    (* populate offsets *)
  let _ =
    List.fold_left
      (fun (p, o) (_, b) ->
        Hashtbl.add offsets p o;
        (p + 1, o + (if b then 2 else 1))
      )
      (0, 0)
      prog
  in
  let f (v: string) : BinNums.coq_Z =
    try
      let v' = getlabel v in
    try
      let w' = Hashtbl.find offsets v' in
      let w = Camlcoq.Z.of_sint w' in
      w
      with Not_found ->
        Printf.printf "Not_found: %i\n" v';
        exit(-1)
      with Not_found ->
        Printf.printf "Not_found: %s\n" v;
        exit(-1)
  in
    (* change offsets *)
    List.map (fun (i, _) -> i f) prog

