(* Copyright (c) 2013, IMDEA Software Institute.            *)
(* See ./LICENSE for authorship and licensing information   *)

open AsmUtil
open X86Headers
open Config

let bin_name = ref ""
let start_addr = ref(-1 )
let end_addr = ref 0
let data_cache_s = ref 0
let data_line_s = ref 0
let data_assoc = ref 0
let inst_cache_s = ref 0
let inst_line_s = ref 0
let inst_assoc = ref 0
let data_cache_strategy = ref CacheAD.LRU
let inst_cache_strategy_opt = ref None

let instruction_base_addr = ref (Int64.of_int 0)

let print_cfg = ref false
let print_ass = ref false
let analyze = ref true
let interval_cache = ref false
let do_traces = ref false


type cache_age_analysis = IntAges | SetAges | OctAges | RelAges

let data_cache_analysis = ref SetAges
let inst_cache_analysis_opt = ref None

let temp_log_level = ref ""

let cache_size = ref 0
let line_size = ref 0
let associativity = ref 0

type attacker_model = Final 
  | Instructions of int (* may interrupt each x instruction *)
  | OneInstrInterrupt
  | OneTimedInterrupt

let attacker = ref Final

type architecture_model = Joint | Split | NoInstructionCache

let architecture = ref NoInstructionCache

let more_to_parse b = more b && (!end_addr=0 || get_byte b <= !end_addr)

(*let debug bits =
  let nubits=goto bits !start_addr in
  Format.printf "Address %Lx\n" (fst (AsmUtil.read_uint32 nubits 32))*)

let read_assembly bits =
  let rec read_instr_list b =
    if more_to_parse b then
      let addr = get_byte b in
      let i,nb = X86Parse.read_instr b in
      match i with
    X86Types.Ret -> [(addr,i)]
      | _ -> (addr, i)::read_instr_list nb
    else []
  in read_instr_list (goto bits !start_addr)


let print_assembly bs = 
    List.iter (function (n,b) -> Format.printf "@<6>%n\t%x\t%a@\n" n n X86Print.pp_instr b) bs
    
let usage = "Usage: " ^ Sys.argv.(0) ^ " BINARY [OPTION]"
(* function which handles binary names (anonymous arguments) *)
let anon_fun = (fun x ->  if !bin_name = "" then bin_name := x
               else raise (Arg.Bad ("The binary name is specified a second time: " ^ x)))

let speclist = [
    (* ("-f", Arg.String anon_fun, "give the name of the binary file"); *)
    ("--start", Arg.String (fun s -> start_addr := int_of_string s), 
      "set the address (in bytes) where to start parsing");
    ("--end", Arg.String (fun s -> end_addr := int_of_string s), 
      "set the oddress (in bytes) where to stop parsing");
    ("--cfg", Arg.Unit (fun () -> print_cfg := true; analyze := false;), 
      "prints the control flow graph only, no analysis performed"
      ^"\n  Options for data cache configuration:");
    ("--cache-size", (Arg.Int (fun n -> data_cache_s := n)),
      "set the cache size (in bytes)");
    ("--line-size", (Arg.Int (fun n -> data_line_s := n)), 
      "set the cache line size (in bytes)");
    ("--assoc", (Arg.Int (fun n -> data_assoc := n)),
     "set the cache associativity");
    ("--lru", Arg.Unit (fun () -> data_cache_strategy := CacheAD.LRU), 
      "set the cache replacement strategy to LRU (default)");
    ("--fifo", Arg.Unit (fun () -> data_cache_strategy := CacheAD.FIFO), 
      "set the cache replacement strategy to FIFO");
    ("--plru", Arg.Unit (fun () -> data_cache_strategy := CacheAD.PLRU), 
      "set the cache replacement strategy to PLRU");
    ("--interval-cache", Arg.Unit (fun () -> data_cache_analysis := IntAges), 
      "use the interval abstract domain for the cache") ;
    ("--rset-cache", Arg.Unit (fun () -> data_cache_analysis := RelAges), 
      "use the relational set abstract domain for the cache") ;
    ("--oct-cache", Arg.Unit (fun () -> data_cache_analysis := OctAges), 
      "use the octagon abstract domain for the cache"
       ^"\n  Options for instruction caches (default are data cache options):");
    ("--inst-cache", Arg.Unit (fun () -> architecture := Split),
     "enable instruction cache tracking (separate caches for data and instructions)");
    ("--shared-cache", Arg.Unit (fun () -> architecture := Joint), 
     "enable instruction cache tracking (shared caches for data and instructions");
    ("--inst-cache-size", (Arg.Int (fun n -> inst_cache_s := n)),
     "set the instruction cache size (in bytes)");
    ("--inst-line-size", (Arg.Int (fun n -> inst_line_s := n)),
     "set the instruction cache line size (in bytes)");
    ("--inst-assoc", (Arg.Int (fun n -> inst_assoc := n)),
     "set the instruction cache associativity");
    ("--inst-interval-cache", Arg.Unit (fun () -> inst_cache_analysis_opt := Some IntAges), 
      "use the interval abstract domain for instruction cache") ;
    ("--inst-rset-cache", Arg.Unit (fun () -> inst_cache_analysis_opt := Some RelAges), 
      "use the relational set abstract domain for instruction cache") ;
    ("--inst-oct-cache", Arg.Unit (fun () -> inst_cache_analysis_opt := Some OctAges), 
      "use the octagon abstract domain for instruction cache") ;
    ("--inst-lru", Arg.Unit (fun () -> inst_cache_strategy_opt := Some CacheAD.LRU), 
      "set the instruction cache replacement strategy to LRU");
    ("--inst-fifo", Arg.Unit (fun () -> inst_cache_strategy_opt := Some CacheAD.FIFO), 
      "set the cache replacement strategy to FIFO");
    ("--inst-plru", Arg.Unit (fun () -> inst_cache_strategy_opt := Some CacheAD.PLRU), 
      "set the cache replacement strategy to PLRU"
      ^"\n  Controlling and disabling aspects of the analysis:");
   
    ("--traces", Arg.Unit (fun () -> do_traces := true),
      "enable tracking of hit/miss traces and execution times");
    ("--unroll", Arg.Int (fun u -> Iterator.unroll_count:=u), "number of loop unrollings");
    ("--no-outer-unroll", Arg.Unit (fun () -> Iterator.unroll_outer_loop:=false), 
      "overwrites the --unroll option, so that outer loops are not unrolled"
      ^"\n  Logging:");
    ("--log [quiet|normal|debug]",Arg.String (fun level -> Logger.set_global_ll level), 
      "set the general log level. Options are quiet, normal and debug. \
       Default is normal");
    ("--log-one-ad [quiet|normal|debug] SomeAD",Arg.Tuple [Arg.Set_string temp_log_level; 
      Arg.String (fun ad -> Logger.set_ad_ll !temp_log_level ad)], 
      "modify the output of SomeAD, where SomeAD is one of ageAD, architectureAD, cacheAD, flagAD, \
      memAD, stackAD, traceAD, valAD, and iterator");]

let _ =
  Arg.parse speclist anon_fun usage;
  if !bin_name="" then begin
    Format.printf "Error: You need to specify a filename\n";
    exit 1
  end;
  if not (Sys.file_exists !bin_name) then begin
    Format.printf "%s: No such file or directory\n" (!bin_name);
    exit 1
  end;
  let start_values =
    begin
      try
        let sa,sv,cp = Config.config (!bin_name^".conf") in
        Printf.printf "Configuration file %s.conf parsed\n" !bin_name;
        (match sa with
        | None -> Printf.printf "Start address not specified\n"
        | Some x -> Printf.printf "Start address is 0x%x\n" x; start_addr := x);
          instruction_base_addr := cp.inst_base_addr;
          data_cache_s := if !data_cache_s <= 0 then cp.cache_s else !data_cache_s;
          data_line_s := if !data_line_s <= 0 then cp.line_s else !data_line_s;
          data_assoc := if !data_assoc <= 0 then cp.assoc else !data_assoc;
          inst_cache_s := if !inst_cache_s <= 0 then cp.inst_cache_s else !inst_cache_s;
          inst_line_s := if !inst_line_s <= 0 then cp.inst_line_s else !inst_line_s;
          inst_assoc := if !inst_assoc <= 0 then cp.inst_assoc else !inst_assoc;
          sv
      with Sys_error _ ->
        Printf.printf "Configuration file %s.conf not found\nUsing default values\n" !bin_name;
        ([],List.map (fun (a,b) -> a,b,b) [(X86Types.EAX, 1L); (X86Types.ECX, 0xbffff224L); (X86Types.EDX, 0xbffff1b4L); (X86Types.EBX, 0x2d3ff4L); 
               (X86Types.ESP, 0xbffff18cL); (X86Types.EBP, 0L); (X86Types.ESI, 0L); (X86Types.EDI, 0L)])
    end
  in
  let bits, mem =
      let mem = read_exec !bin_name in
      (* Setting default values *)
      if !start_addr =(-1) then failwith ("No starting address given"); (*start_addr:=starting_offset mem;*)
      if (Int64.compare !instruction_base_addr Int64.zero) = 0 then instruction_base_addr := 139844135157760L;
      if !data_cache_s = 0 then data_cache_s := 16384;
      if !data_line_s = 0 then data_line_s := 64;
      if !data_assoc = 0 then data_assoc := 4;
      if !inst_cache_s = 0 then inst_cache_s := !data_cache_s;
      if !inst_line_s = 0 then inst_line_s := !data_line_s;
      if !inst_assoc = 0 then inst_assoc := !data_assoc;
      Printf.printf "Cache size %d, line size %d, associativity %d\n" !data_cache_s !data_line_s !data_assoc;
      Printf.printf "Offset of first instruction is 0x%x (%d bytes in the file)\n" 
        !start_addr !start_addr;
      (get_bits mem), Some mem in
  if !print_ass then print_assembly (read_assembly bits);
  let data_cache_params = {CacheAD.cs = !data_cache_s; CacheAD.ls = !data_line_s;
    CacheAD.ass = !data_assoc; CacheAD.str = !data_cache_strategy} in
  let inst_cache_strategy = match !inst_cache_strategy_opt with
    | Some v -> ref v 
    | None -> data_cache_strategy in
  let inst_cache_params = {CacheAD.cs = !inst_cache_s; CacheAD.ls = !inst_line_s;
    CacheAD.ass = !inst_assoc; CacheAD.str = !inst_cache_strategy} in
  let inst_cache_analysis = match !inst_cache_analysis_opt with
    | Some v -> ref v
    | None -> data_cache_analysis in
  match mem with
  | None -> ()
  | Some sections ->
    if !print_cfg || Logger.get_log_level Logger.IteratorLL = Logger.Debug then Cfg.printcfg (Cfg.makecfg !start_addr sections);
    if !analyze then begin 
      (* Analysis will be performed. *)
      (* First, the proper abstract domains will be generated, *)
      (* according to the configurations and the command-line arguments *)
       (* function generating a cache AD used for data or instruction caches *)
      let generate_cache cache_analysis attacker =
        let cad = match !cache_analysis with
          | OctAges -> IFDEF INCLUDEOCT THEN 
      (module CacheAD.Make (SimpleOctAD.OctAD) : CacheAD.S) 
            ELSE (failwith "Ocatgon library not included. Try make clean; make oct=1.") END
          | RelAges ->
            (module CacheAD.Make (RelAgeAD.RelAgeAD) : CacheAD.S)
          | (SetAges | IntAges) -> 
            (* Generate the age abstract domain *)
            let age = 
              if !cache_analysis = SetAges then
                (module AgeAD.Make (ValAD.Make(ValAD.ValADOptForMemory)):AgeAD.S)
              else (* !cache_analysis = IntAges *)
                (module AgeAD.Make(ValAD.Make(
                  struct let max_get_var_size = 256 let max_set_size = 0 end)):
                    AgeAD.S) in
            let module Age = (val age: AgeAD.S) in
            (module CacheAD.Make (Age) : CacheAD.S) 
        in
        (* Make distinction whether asynchronous attacker is used  *)
      let module BaseCache = (val cad: CacheAD.S) in
        match !attacker with
        | Final -> cad
        | _ -> failwith "Asynchronous attacker not supported" in
      (* end of generate_cache definition *)
        
      (* Generate the data cache AD, with traces or not *)
      let state = generate_cache data_cache_analysis attacker in
      let datacache = if !do_traces then
    (let module CState = (val state : CacheAD.S) in
     (module TraceAD.Make (CState) : CacheAD.S))
  else state in
      let module DataCache = (val datacache : CacheAD.S) in
      (* Generate the memory AD *)
      let module Mem = MemAD.Make(FlagAD.Make(ValAD.Make(ValAD.ValADOptForMemory)))(DataCache) in
      (* Generate the stack AD *)
      let module Stack = StackAD.Make(Mem) in
      (* Generate the architecture AD *)
      let arch = match !architecture with
        | Split -> let cad = generate_cache inst_cache_analysis attacker in
          let module InstCache = (val cad: CacheAD.S) in
          (module ArchitectureAD.MakeSeparate(Stack)(InstCache): ArchitectureAD.S)
        | Joint -> (module ArchitectureAD.MakeShared(Stack): ArchitectureAD.S)
        | NoInstructionCache -> 
          (module ArchitectureAD.MakeDataOnly(Stack): ArchitectureAD.S) in
      let module Architecture = (val arch: ArchitectureAD.S) in
      (* Generate iterator *)
      let module Iter = Iterator.Make(Architecture) in
      let iterate = Iter.iterate in
      let start = Sys.time () in 
      (* Run the analysis *)
      iterate sections start_values data_cache_params (Some(inst_cache_params)) !instruction_base_addr (Cfg.makecfg !start_addr sections);
      Printf.printf "Analysis took %d seconds.\n" (int_of_float (Sys.time () -. start))
    end
