module L = LatticeSignatures

let rec omega = Datatypes.S omega

type crit =
  | Mem of Camlcoq.Z.t
  | Reg0
  | NoCrit

type widen =
  | BackEdge
  | Delay
  | NoWiden

type config =
  { source : string
  ; fin_set: bool
  ; debug  : bool
  ; mdebug : bool
  ; dumpsrc: bool
  ; dumpbin: bool
  ; widening: widen
  ; fuel   : Datatypes.nat
  ; vp     : crit
  ; unroll : bool
  ; run    : string option
  }

let get_args prog =
  begin
  let fn = ref None in
  let criterion = ref NoCrit in
  let vp str =
    match !criterion with
    | NoCrit ->
        (criterion := try Mem (Camlcoq.Z.of_sint (int_of_string str)) with _ -> Reg0)
    | _ -> prerr_string "Ignored -vp ";
           prerr_string str;
           prerr_newline ()
  in
  let unr = ref false in
  let finset = ref false in
  let dbg = ref false in
  let mdbg = ref false in
  let dmp  = ref false in
  let dmpb = ref false in
  let nfuel = ref omega in
  let fl i = nfuel := Camlcoq.Nat.of_int i in
  let wide = ref BackEdge in
  let get_run, set_run =
    let r : string option ref = ref None in
      ((fun () -> !r),
       fun s -> match !r with
         | None -> r := Some s
         | Some _ -> prerr_endline ("Ignored: -run " ^ s)
      ) in
  let usage = "Usage: " ^ prog
  ^ " [-fin-set] [-vp addr] [-unroll] [-debug] [-mem-debug] [-dump] [-fuel n] [-delay-widen|-no-widen] [-run input] source" in
  Arg.parse
    [ "-vp", Arg.String vp, "value partitionning"
    ; "-unroll", Arg.Set unr, "unroll the CFG"
    ; "-fin-set", Arg.Set finset, "finite sets"
    ; "-debug", Arg.Set dbg, "verbose numerical domain"
    ; "-mem-debug", Arg.Set mdbg, "verbose memory domain"
    ; "-dump", Arg.Set dmp, "dump parsed source"
    ; "-dbin", Arg.Set dmpb, "dump encoded source"
    ; "-fuel", Arg.Int fl, "fuel (default: ω)"
    ; "-delay-widen", Arg.Unit (fun () -> wide := Delay), "delay widening"
    ; "-no-widen", Arg.Unit (fun () -> wide := NoWiden), "disable widening"
    ; "-run", Arg.String set_run, "concrete execution"
    ]
    (fun s ->
       match !fn with
       | None -> fn := Some s
       | Some _ -> prerr_string "Ignored argument: ";
                   prerr_endline s)
    usage;
  match !fn with
  | Some f ->
      { source = f
      ; fin_set = !finset
      ; mdebug = !mdbg
      ; dumpsrc = !dmp
      ; dumpbin = !dmpb
      ; fuel = !nfuel
      ; vp = !criterion
      ; unroll = !unr
      ; widening = !wide
      ; debug = !dbg
      ; run = get_run ()
      }
  | None ->
      prerr_endline usage;
      exit(-1)
  end

let parse_file file =
  let c = open_in file in
  let lb = Lexing.from_channel c in
    try
      let f = Parser.prog Lexer.token lb in
        close_in c;
        f
    with
    | Lexer.Lexical_error s -> 
        Utils.report_loc file (Lexing.lexeme_start_p lb, Lexing.lexeme_end_p lb);
        Format.eprintf "lexical error: %s\n@." s;
        exit 1
    | Parsing.Parse_error ->
        Utils.report_loc file (Lexing.lexeme_start_p lb, Lexing.lexeme_end_p lb);
        Format.eprintf "syntax error\n@.";
        exit 1
    | e ->
        Format.eprintf "Anomaly: %s\n@." (Printexc.to_string e);
        exit 2

let widen_on_backedge (from: Camlcoq.Z.t) (dest: (_, _) GotoAnalysis.ab_post_res) : bool =
  match dest with
  | GotoAnalysis.Run (pp, _) ->
      BinInt.Z.leb pp from
  | _ -> false

let delay k w =
  let tbl = Hashtbl.create 17 in
  fun from dest ->
    let key =
      (from, (match dest with
       | GotoAnalysis.Run (pp, _) -> pp
       | _ -> Integers.Int.zero
      )) in
    let n = try Hashtbl.find tbl key - 1 with Not_found -> k in
      if n > 0
      then
        (
          Hashtbl.add tbl key n;
          false
        )
      else
        w from dest

let exec input mem fuel =
  let mem = ref mem in
  let ic = open_in input in
  begin
  try
    Scanf.fscanf ic "%d %d" (fun a v ->
      Printf.printf "Read: %d %d\n" a v;
      let a = Integers.Int.repr (Camlcoq.Z.of_sint a) in
      let v = Integers.Int.repr (Camlcoq.Z.of_sint v) in
      mem := GotoSem.upd_mem !mem a v
    )
  with _ -> ()
  end;
  close_in ic;
  let open EvalGoto in
  let res =
  match run !mem fuel with
  | Ans v -> Camlcoq.Z.to_string (Integers.Int.signed v)
  | Wrong -> "WRONG"
  | TimeOut _ -> "Time Out"
  in
    Printf.printf "Exec: %s\n" res

let () =
  let conf = get_args Sys.argv.(0) in
    Printf.printf "Conf: %s%s%s%s%s\n"
      conf.source
      (if conf.fin_set then " FinSet" else "")
      (match conf.vp with
       | Mem vp -> " mem partition on " ^ Camlcoq.Z.to_string vp
       | Reg0   -> " partition on R0"
       | NoCrit -> "")
      (if conf.debug then " debug" else "")
      (match conf.widening with
       | NoWiden -> " no widening"
       | Delay   -> " delayed widening"
       | BackEdge -> ""
      )
      ;
  let dom = if conf.fin_set then FirstGotoAnalysis.ND_FinSet else FirstGotoAnalysis.ND_SSI in
  let dom = if conf.debug then FirstGotoAnalysis.ND_Debug dom else dom in
  let string_of_dom v =
    Camlcoq.camlstring_of_coqstring (FirstGotoAnalysis.string_of_dom dom v) in
  let prog = parse_file conf.source in
    if conf.dumpsrc
    then Utils.print_prog prog
      ;
  let (mem,footprint) = GotoSem.encode_program prog (fun _ -> Integers.Int.zero) in
  if conf.dumpbin
  then Utils.print_bin mem (List.rev footprint);
  (match conf.run with
   | Some input -> exec input mem conf.fuel;
                   exit 0
   | None -> ()
  );
  let max_deref = BinNums.Npos (Camlcoq.P.of_int 100) in
  let widen_oracle =
    match conf.widening with
    | BackEdge -> widen_on_backedge
    | Delay -> delay 1 widen_on_backedge
    | NoWiden -> fun _ _ -> false
  in
  match conf.vp with
  | NoCrit ->
    begin
  let res = FirstGotoAnalysis.first_vsa
              dom
              conf.mdebug
              max_deref
              widen_oracle
              mem
              footprint
              conf.fuel
  in
    begin
    match res with
    | GotoAnalysis.Coq_ipvsa_top ->
        Printf.printf "Top!\n"
    | GotoAnalysis.Coq_ipvsa_fix e ->
        Printf.printf "Fixpoint found. %s. "
          begin
            if FirstGotoAnalysis.first_validate dom false max_deref mem footprint e
            then "VALID"
            else "Maybe NOT valid?"
          end;
        begin
        match FirstGotoAnalysis.first_compute_cfg dom false max_deref footprint e conf.fuel with
        | Some g ->
            let fo = open_out "graph.dot" in
              Printf.fprintf fo "%s" (Utils.dump_cfg string_of_dom g);
              close_out fo
        | None -> Printf.fprintf stderr "cfg broke\n"
        end;
        if FirstGotoAnalysis.first_check_safety dom conf.mdebug max_deref footprint e
        then print_endline "SAFE!"
        else print_endline "Maybe unsafe."
    | GotoAnalysis.Coq_ipvsa_cont _ ->
        Printf.printf "Dame màs gasolina.\n"
    end;
    end
    | _ ->
        begin
       let partition =
         match conf.vp with
         | Mem crit -> FirstGotoAnalysis.mem_cell_partition dom conf.mdebug footprint crit
         | _ -> FirstGotoAnalysis.reg_partition dom conf.mdebug footprint Goto.R0
       in
       if conf.unroll
       then (begin
       let res = FirstGotoAnalysis.analysis
                   dom
                   conf.mdebug
                   max_deref
                   widen_oracle
                   mem
                   footprint
                   partition
                   conf.fuel in
         match res with
         | Some cfg ->
             let fo = open_out "graph.dot" in
               Printf.fprintf fo "%s" (Utils.dump_cfg2 string_of_dom cfg);
               close_out fo
         | None -> print_endline "Oops"
             end)
       else (begin
       let res = FirstGotoAnalysis.vp_analysis
                   dom
                   conf.mdebug
                   max_deref
                   widen_oracle
                   mem
                   footprint
                   partition
                   conf.fuel in
         match res with
         | GotoAnalysis.VP_top -> print_endline "Top"
         | GotoAnalysis.VP_cont _ -> print_endline "Gave up"
         | GotoAnalysis.VP_fix e ->
             print_string
               ("Found a fixpoint! "
               ^
               (if FirstGotoAnalysis.vp_validate dom conf.mdebug max_deref mem footprint partition e
                then "VALID! "
                else "Maybe invalid ")
               ^
               (if FirstGotoAnalysis.vp_check_safety dom conf.mdebug max_deref footprint e
                then "SAFE! "
                else "Maybe unsafe ")
               );
             begin
               match FirstGotoAnalysis.vp_compute_cfg dom conf.mdebug max_deref footprint e conf.fuel with
               | Some g ->
                   let fo = open_out "graph.dot" in
                     Printf.fprintf fo "%s" (Utils.dump_cfg string_of_dom g);
                     close_out fo
               | None -> Printf.fprintf stderr "cfg broke\n"
             end
             end)
     end;
    Printf.printf "Fini.\n"

  (*
let string_of_flg = function
  | None -> "T"
  | Some ((x,y)) ->
      "(" ^ (string_of_register x) ^ ", " ^
      (string_of_register y) ^ ")"

let str_of_bind f k v z =
  match Lattice_def.EquivDec.dec (Si_def.coq_RSI_Equiv Si_sem.k) v (Some
  (Si_def.si_top Si_sem.k)) with
  | true -> z
  | false ->
      Printf.sprintf "%s[%s↦ %s] " z (f k)
      (Ast_utils.string_of_option Si_utils.string_of_si v)

let string_of_ab_mc alc (m:Goto.ab_machine_config): string =
  "{\n  Flg: "^(string_of_flg (Goto.ab_flg m))
  ^"\n  Reg: "^(Goto.print_reg (str_of_bind string_of_register) (Goto.ab_reg m) "")
  ^"\n  Mem: "^(Goto.print_mem alc
    (str_of_bind (Int32.to_string @@ int32_of_z))
    (Goto.ab_mem m) "")
  ^"\n}"

let print alc e =
  let (run, hlt) =
    Goto.print_env
    (fun k e a -> a ^
    (Int32.to_string (int32_of_z k)) ^ " |-> "
    ^ (Ast_utils.string_of_option (string_of_ab_mc alc) e) ^ "\n")
    (Ast_utils.string_of_option Si_utils.string_of_si)
    (Goto.result e) ""
  in Printf.printf "****\nRun:\n%s\nHlt: %s\n****\n"
  run hlt

let print_at alc e =
  match Goto.worklist e with
  | n::_ ->
      Printf.printf "%s: %s\n" (Zutils.string_of_z n)
      begin
      match Goto.result_at_run e n with
      | Some ab_mc -> string_of_ab_mc alc ab_mc
      | None -> "⊤"
      end
  | [] -> ()

let step_by_step max_deref max_ind alocs woracle i =
  let rec aux = function
    | Goto.Coq_ipvsa_cont e ->
        print_at alocs e;
        aux (Goto.intraProceduralVSA_step max_deref max_ind alocs woracle e)
    | t -> t
  in
  let st = Goto.intraProceduralVSA_init alocs i in
  aux (Goto.Coq_ipvsa_cont st)

let () =
  let f =
    try
      begin
      let file = Sys.argv.(1) in
  in
  (*let alocs = ref (List0.rev_append def_alocs initial_alocs) in*
  let alocs = ref initial_alocs in
  let num_alocs = ref (int_of_nat (length !alocs)) in
  for i = 0 to max_Iter do
    more_hint ();
    Printf.printf "Alocs (%d): " !num_alocs;
    List0.fold_left
      (fun () (l:coq_Value) -> Printf.printf "%s " (Int32.to_string
      (int32_of_z l)))
      !alocs ();
    match S_by_s.intraProceduralVSA f !alocs max_deref (widen_oracle f) (pos_of_int max_iter) with
    | Vsa_res_fix (p, e) -> Ast_utils.print_abEnv f e ;
        Printf.printf "\nAfter %d\n" (max_iter - (int_of_pos p));
        let new_alocs = *Coq_cons (z_of_int (-40), Coq_cons (z_of_int (-32),
         Coq_cons (z_of_int (-28), (Coq_cons (z_of_int (-24),* find_alocs f e in
        let new_num = int_of_nat (length new_alocs) in
        if new_num > !num_alocs
        then begin
          alocs := *List0.rev_append def_alocs* new_alocs ;
          num_alocs := new_num *;
          ignore (step_by_step f !alocs 460);
          exit(0*
        end
        else begin
          Printf.printf "%s\n" (
          match validate_fix_point f e !alocs max_deref with
          | Coq_true -> "Fini !"
          | Coq_false -> "AAAARGH"
          );
          exit(0)
        end

    | Vsa_res_cont e -> Ast_utils.print_abEnv f e.result ;
      print_string "De seguir…\n";
      exit (0)
  done *)
let mem = Goto.encode_program f (fun _ -> z_of_int 0)
and alc = z_of_int 100 :: z_of_int 101 :: z_of_int 102 :: z_of_int 1000 ::  Goto.prog_alocs f in
Shared.more_hint ();
    let max_deref = z_of_int 4 in
    let max_ind = max_deref in
    (*
    let vsa_res = step_by_step max_deref max_ind alc Shared.widen_oracle1 mem
  *)
  let vsa_res = Goto.intraProceduralVSA max_deref max_ind alc
  Shared.widen_oracle1 mem (nat_of_int 1000)
  in match vsa_res with
    | Goto.Coq_ipvsa_top -> print_string "TOP !\n"
    | Goto.Coq_ipvsa_cont _ -> print_string "No fix-point reached\n"
    | Goto.Coq_ipvsa_fix e ->
        print alc e;
        print_newline();
        (match Goto.validate_fix_point max_deref max_ind alc mem (Goto.result e) with
        | true  -> print_string "\nSound fix-point reached\n";
                   if Goto.check_safety (Goto.result e)
                   then print_endline "Program is SAFE"
                   else print_endline "Cannot prove the program safety";
          (match CFG.compute_cfg (fst (Goto.result e)) max_deref max_ind alc
          (let rec omega = S omega in omega)
          with Some g ->
            let fo = open_out "graph.dot" in
            Printf.fprintf fo "%s" (Ast_utils.dump_cfg g);
            close_out fo
          | None -> Printf.fprintf stderr "cfg broke")
          | false -> print_string "\nCould not check the soundness of the reached fix-point…\n"
        )

   *)
