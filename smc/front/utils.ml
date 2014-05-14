let report_loc file (b,e) =
  let l = b.Lexing.pos_lnum in
  let fc = b.Lexing.pos_cnum - b.Lexing.pos_bol + 1 in
  let lc = e.Lexing.pos_cnum - b.Lexing.pos_bol + 1 in
  Format.eprintf "File « %s », line %d, characters %d-%d:\n" file l fc lc

let string_of_register : Goto.register -> string = function
  | Goto.R0 -> "R0"
  | Goto.R1 -> "R1"
  | Goto.R3 -> "R3"
  | Goto.R2 -> "R2"
  | Goto.R4 -> "R4"
  | Goto.R5 -> "R5"
  | Goto.R6 -> "R6"
  | Goto.R7 -> "R7"

let string_of_flag : Goto.flag -> string = function
  | Goto.FLE -> "LE"
  | Goto.FLT -> "LT"
  | Goto.FEQ -> "EQ"

let string_of_botlift (f: 'a -> string) : 'a AdomLib.botlift -> string =
  function
  | AdomLib.NotBot s -> f s
  | AdomLib.Bot -> "⊥"

let string_of_option (f: 'a -> string) : 'a option -> string =
  function
  | Some a -> f a
  | None -> "⊥"

let string_of_instr : Goto.instruction -> string =
  let p = Printf.sprintf in function
  | Goto.ICst (n,r) -> p "cst %s → %s" (Camlcoq.Z.to_string (Integers.Int.signed n)) (string_of_register r)
  | Goto.IBinop (o, s,d) -> p "%s %s → %s"
                              (Camlcoq.camlstring_of_coqstring (DebugAbMachineNonrel.string_of_int_binop o))
                              (string_of_register s) (string_of_register d)
  | Goto.ICmp (s,d) -> p "cmp %s, %s" (string_of_register s) (string_of_register d)
  | Goto.ISkip -> "skip"
  | Goto.IHalt r -> p "halt %s" (string_of_register r)
  | Goto.IGoto l -> p "goto %s" (Camlcoq.Z.to_string l)
  | Goto.IGotoCond (f, l) -> p "goto%s %s" (string_of_flag f) (Camlcoq.Z.to_string l)
  | Goto.IGotoInd r -> p "goto %s" (string_of_register r)
  | Goto.IStore (s,d) -> p "store %s → *%s" (string_of_register s) (string_of_register d)
  | Goto.ILoad (s,d) -> p "load *%s → %s" (string_of_register s) (string_of_register d)

let print_prog (p: Goto.instruction list) : unit =
  List.iter
    (fun i -> print_endline (string_of_instr i))
    p

let string_of_ab_instr (f: 'a -> string) : 'a GotoAnalysis.ab_instruction -> string =
  let p = Printf.sprintf in function
  | GotoAnalysis.AICst (n,r) -> p "cst %s → %s" (f n) (string_of_register r)
  | GotoAnalysis.AIBinop (o, s,d) -> p "%s %s → %s"
                              (Camlcoq.camlstring_of_coqstring (DebugAbMachineNonrel.string_of_int_binop o))
                              (string_of_register s) (string_of_register d)
  | GotoAnalysis.AICmp (s,d) -> p "cmp %s, %s" (string_of_register s) (string_of_register d)
  | GotoAnalysis.AISkip -> "skip"
  | GotoAnalysis.AIHalt r -> p "halt %s" (string_of_register r)
  | GotoAnalysis.AIGoto l -> p "goto %s" (f l)
  | GotoAnalysis.AIGotoCond (flg, l) -> p "goto%s %s" (string_of_flag flg) (f l)
  | GotoAnalysis.AIGotoInd r -> p "goto %s" (string_of_register r)
  | GotoAnalysis.AIStore (s,d) -> p "store %s → *%s" (string_of_register s) (string_of_register d)
  | GotoAnalysis.AILoad (s,d) -> p "load *%s → %s" (string_of_register s) (string_of_register d)

let node_of_int z : string =
  Printf.sprintf "_%s" (Camlcoq.Z.to_string z)

let node_of_int_pair z : string =
  Printf.sprintf "_%s_%s" (Camlcoq.Z.to_string (fst z)) (Camlcoq.Z.to_string (snd z))

let dump_edge f i (succ: (AbCfg.node * 'a GotoAnalysis.ab_instruction option) list) : string =
  Printf.sprintf
  "%s"
  (List.fold_left
  (fun s j ->
    Printf.sprintf "%s%s -> %s [label=\"%s\"]\n"
    s
    (node_of_int i)
    (node_of_int (fst j))
    (string_of_option (string_of_ab_instr f) (snd j)))
  ""
  succ)

let dump_edge2 f i (succ: (AbCfg2.node * 'a GotoAnalysis.ab_instruction option) list) : string =
  Printf.sprintf
  "%s"
  (List.fold_left
  (fun s j ->
    Printf.sprintf "%s%s -> %s [label=\"%s\"]\n"
    s
    (node_of_int_pair i)
    (node_of_int_pair (fst j))
    (string_of_option (string_of_ab_instr f) (snd j)))
  ""
  succ)

let dump_cfg f (g: 'a AbCfg.node_graph) : string =
  Printf.sprintf "digraph {\n%s%s}"
  (AbCfg.cfg_fold
  (fun i ->
    function
      (_, b) ->
        fun z ->
          Printf.sprintf "%s%s [label=\"%s\", shape=%s]\n" z
          (node_of_int i)
          (Camlcoq.Z.to_string (Integers.Int.signed i))
          (if b then "doublecircle" else "circle")
          )
  g
  ""
  )
  (AbCfg.cfg_fold
  (fun i ->
    function
      (succ, _) ->
        fun z ->
          Printf.sprintf "%s%s" z
          (dump_edge f i succ)
          )
  g
  ""
  )

let dump_cfg2 f (g: 'a AbCfg2.node_graph) : string =
  Printf.sprintf "digraph {\n%s%s}"
  (AbCfg2.cfg_fold
  (fun i ->
    function
      (_, b) ->
        fun z ->
          Printf.sprintf "%s%s [label=\"%s\", shape=%s]\n" z
          (node_of_int_pair i)
          (Camlcoq.Z.to_string (Integers.Int.signed (fst i)))
          (if b then "doublecircle" else "circle")
          )
  g
  ""
  )
  (AbCfg2.cfg_fold
  (fun i ->
    function
      (succ, _) ->
        fun z ->
          Printf.sprintf "%s%s" z
          (dump_edge2 f i succ)
          )
  g
  ""
  )


let print_bin (m: GotoSem.memory) (l: Camlcoq.Z.t list) : unit =
  List.iter (fun n -> print_endline (Camlcoq.Z.hex (m n))) l
