open Cil_types
open Cilutil
open Cil
open SccCallgraph 
open Callgraph
open CustomTaintFlow
open TaintResults
open MinReadMetrics
open MaxReadMetrics
open MinTaintMetrics
open MaxTaintMetrics
open Visitor

let option_enabled () = "taint-analysis.enabled"
let option_print_intermediate () = "taint-analysis.print-intermediate"
let option_print_final () = "taint-analysis.print-final"
let option_print_source () = "taint-analysis.print-source"
let option_do_results () = "taint-analysis.do-results"
let option_print_vulnerable_source () = "taint-analysis.print-vulnerable"
let option_config_file () = "taint-analysis.config-file"
let option_constr_config_file () = "taint-analysis.constr-config-file"
let option_debugging () = "taint-analysis.debug"
let option_info () = "taint-analysis.info"
let option_prepare_slice () = "taint-analysis.prepare-slice"
let option_min_read_metric () = "taint-analysis.min-read-metric"
let option_max_read_metric () = "taint-analysis.max-read-metric"
let option_min_taint_metric () = "taint-analysis.min-taint-metric"
let option_max_taint_metric () = "taint-analysis.max-taint-metric"

(* TESTING *)
let option_test_ptranal () = "taint-analysis.ptranal"

let option_main_function () = "taint-analysis.main-function"

let default_config_file () = "default.cfg"
let default_constr_config_file () = "default_constr.cfg"

(* Register a new Frama-C option. *)
module Enabled =
    Cmdline.Dynamic.Register.False(struct let name = option_enabled () end)

(* Register a new Frama-C option. *)
module PrintIntermediateEnabled =
    Cmdline.Dynamic.Register.False(struct let name = option_print_intermediate () end)
    
(* Register a new Frama-C option. *)
module PrintFinalEnabled =
    Cmdline.Dynamic.Register.False(struct let name = option_print_final () end)
    
(* Register a new Frama-C option. *)
module PrintSourceEnabled =
    Cmdline.Dynamic.Register.False(struct let name = option_print_source () end)
    
(* Register a new Frama-C option. *)
module DoResultsEnabled =
    Cmdline.Dynamic.Register.False(struct let name = option_do_results () end)
    
module PrintVulnerableSourceEnabled =
    Cmdline.Dynamic.Register.False(struct let name = option_print_vulnerable_source () end)

module Debugging = 
    Cmdline.Dynamic.Register.False(struct let name = option_debugging () end)

module Info = 
    Cmdline.Dynamic.Register.False(struct let name = option_info () end)
                                                                                                                                                
(* Register config file sub option. *)
module ConfigFile =
    Cmdline.Dynamic.Register.EmptyString(struct let name = option_config_file () end)
    
(* Register constraint config file sub option. *)
module ConstrConfigFile =
    Cmdline.Dynamic.Register.EmptyString(struct let name = option_constr_config_file () end)

(* Register main function name sub option. *)
module MainFunction =
    Cmdline.Dynamic.Register.EmptyString(struct let name = option_main_function () end)
	
(* Register prepare slice sub option. *)
module PrepareSliceEnabled =
    Cmdline.Dynamic.Register.False(struct let name = option_prepare_slice () end)
    
(* Register read metric sub option. *)
module MinReadMetricEnabled =
    Cmdline.Dynamic.Register.False(struct let name = option_min_read_metric () end)

(* Register read metric sub option. *)
module MaxReadMetricEnabled =
    Cmdline.Dynamic.Register.False(struct let name = option_max_read_metric () end)
    
(* Register min taint metric sub option. *)
module MinTaintMetricEnabled =
    Cmdline.Dynamic.Register.False(struct let name = option_min_taint_metric () end)
    
(* Register max taint metric sub option. *)
module MaxTaintMetricEnabled =
    Cmdline.Dynamic.Register.False(struct let name = option_max_taint_metric () end)

(* TESTING *)
module PtranalEnabled = 
    Cmdline.Dynamic.Register.False(struct let name = option_test_ptranal () end)
    
let run_taint fmt debug info config_file_name constr_config_file_name globals =
    let module P = TaintPrinter.Printer(struct
                                        let fmt = fmt
                                        let debug = debug
                                        let info = info
                                    end) in   
    let computed_function_envs = ref (Inthash.create 1024) in
    let func_hash = Hashtbl.create 1024 in
    let lib_func_hash = Inthash.create 1024 in
    let func_constr_hash = Inthash.create 1024 in
    List.iter
        (fun global ->
            match global with
            | GFun (funcdec, _) -> Hashtbl.add func_hash funcdec.svar.vname funcdec
            | _ -> ignore ())
        globals;
    let print_function_count () =
        ignore ()
    in
    let intialize_library_calls () =
        TaintConfigHelper.run_library fmt debug info config_file_name constr_config_file_name
            computed_function_envs globals (ref func_hash) (ref lib_func_hash) (ref func_constr_hash)
    in    
    let perform_analysis print_intermediate =
        let main_func =
            match MainFunction.is_set () with
                | true -> Some (MainFunction.get ())
                | false -> None in
        let (mappings, nodes, g, lst) = SccCallgraph.get_scc () in
        let get_function node = 
            let n = Hashtbl.find mappings node in
            let fname = nodeName n.cnInfo in
            Utils.get_function_by_name globals fname
        in
        let rec next_func component =
            match SccCallgraph.get_next_call mappings nodes g component with
            | FuncNone -> ignore ()
            | FuncNonRecursive (node, remaining) -> 
                (match get_function node with
                | None -> next_func remaining
                | Some func ->
                    run_custom_taint_non_recursive fmt debug info print_intermediate 
                        func computed_function_envs func_hash globals main_func)
            | FuncRecursive node_list -> 
                let func_list = List.fold_left 
                                    (fun res node 
                                        -> 
                                            match get_function node with
                                            | None -> res
                                            | Some func -> List.concat [res;[func]]) 
                                    []
                                    node_list in
                run_custom_taint_recursive fmt debug info print_intermediate
                    func_list computed_function_envs func_hash globals main_func
        in
        List.iter next_func lst;
    in
    let print_results enabled =
        if enabled then (
            Inthash.iter
                (fun id (env, _) ->
                    try
	                    let _ = Inthash.find lib_func_hash id in
	                        ignore ()
                    with Not_found ->
	                    let vinfo = varinfo_from_vid id in
			            P.print () "\nEnvironment for function %s:\n" vinfo.vname;
			            P.print_env () env)
            (!computed_function_envs)
        )
    in
    let print_source enabled =
        if enabled then 
            Cil.dumpFile (new TaintPretty.print !computed_function_envs) stdout "test" (Cil_state.file ())
    in
    let do_results enabled =
        if enabled then
            match get_results fmt debug info !computed_function_envs func_hash 
	                globals (Inthash.create 1024) with
            | (stmt_count, taint_stmt_count, _) ->
                P.print () "STMT_COUNT: %d TAINT_STMT_COUNT: %d\n" stmt_count taint_stmt_count
    in
    let print_vulnerable_source enabled =
        if enabled then
          match get_results fmt debug info !computed_function_envs func_hash
                    globals func_constr_hash with
          | (_, _, vulnerable_statements) ->
                VulnerablePrinter.print vulnerable_statements fmt debug info
    in    
    let do_prepare_slice enabled = 
        if enabled then
            P.print () "%s\n" "ERROR: This option is deprecated and has been removed!"
            (* match get_results fmt debug info !computed_function_envs func_hash 
                    globals func_constr_hash with
            | (_, _, vulnerable_statements) ->
                Cil.dumpFile (new SlicePretty.print vulnerable_statements) stdout "test" (Cil_state.file ());*)
    in
    let do_min_read_metrics enabled =
        if enabled then (
            let stmt_hash = compute_min_read_metrics fmt debug info func_hash in
            Cil.dumpFile (new MetricPretty.print stmt_hash) stdout "test" (Cil_state.file ())
        )
    in
    let do_max_read_metrics enabled =
        if enabled then (
            let stmt_hash = compute_max_read_metrics fmt debug info func_hash in
            Cil.dumpFile (new MetricPretty.print stmt_hash) stdout "test" (Cil_state.file ())
        )
    in
    let do_min_taint_metrics enabled =
        if enabled then (
            let stmt_hash = compute_min_taint_metrics fmt debug info func_hash !computed_function_envs in
            Cil.dumpFile (new MetricPretty.print stmt_hash) stdout "test" (Cil_state.file ())
        )
    in
    let do_max_taint_metrics enabled =
        if enabled then (
            let stmt_hash = compute_max_taint_metrics fmt debug info func_hash !computed_function_envs in
            Cil.dumpFile (new MetricPretty.print stmt_hash) stdout "test" (Cil_state.file ())
        )
    in
    (* TESTING *)
    let do_ptranal enabled =
        if enabled then (
            visitFramacFile (new TestPointsTo.visitor) (Cil_state.file())
        )
    in
    
    print_function_count ();
    intialize_library_calls ();
    P.print_info () "%s\n" "Performing Taint Analysis";
    perform_analysis (PrintIntermediateEnabled.get ());
    P.print_info () "%s\n" "Printing Results";
    print_results (PrintFinalEnabled.get ());
    P.print_info () "%s\n" "Printing Annotated Source";
    print_source (PrintSourceEnabled.get ());
    P.print_info () "%s\n" "Doing results";
    do_results (DoResultsEnabled.get ());
    P.print_info () "%s\n" "Printing vulnerable source";
    print_vulnerable_source (PrintVulnerableSourceEnabled.get ());
    P.print_info () "%s\n" "Preparing slice";
    do_prepare_slice (PrepareSliceEnabled.get ());
    P.print_info () "%s\n" "Computing min read metrics";
    do_min_read_metrics (MinReadMetricEnabled.get ());
    P.print_info () "%s\n" "Computing max read metrics";
    do_max_read_metrics (MaxReadMetricEnabled.get ());
    P.print_info () "%s\n" "Computing min taint metrics";
    do_min_taint_metrics (MinTaintMetricEnabled.get ());
    P.print_info () "%s\n" "Computing max taint metrics";
    do_max_taint_metrics (MaxTaintMetricEnabled.get ());
    (* TESTING *)
    P.print_info () "%s\n" "Computing points to analysis";
    do_ptranal (PtranalEnabled.get ())

let run fmt =
    if Enabled.get () then
        let file = Cil_state.file () in
        let globals = file.globals in 
        let config_file_name = 
            match ConfigFile.is_set () with
                | true -> ConfigFile.get ()
                | false -> default_config_file () in
        let constr_config_file_name =
            match ConstrConfigFile.is_set () with
                | true -> ConstrConfigFile.get ()
                | false -> default_constr_config_file () in
        run_taint fmt (Debugging.get ()) (Info.get ()) config_file_name constr_config_file_name globals
        
(* Extend the Frama-C command line. *)
let () =
      Options.add_plugin
       ~name:"taint-analysis" (* plug-in name *)
       ~descr:"Taint analysis plugin" (* plug-in description *)
       ["-taint-analysis", (* plug-in option *)
       Arg.Unit Enabled.on,
       ": Compute taint analysis.";
       
       "-print-intermediate", (* plug-in option *)
       Arg.Unit PrintIntermediateEnabled.on,
       ": Print the intermediate results for the taint analysis.";
    
       "-print-final", (* plug-in option *)
       Arg.Unit PrintFinalEnabled.on,
       ": Print the final results for the taint analysis.";
    
       "-print-source", (* plug-in option *)
       Arg.Unit PrintSourceEnabled.on,
       ": Print the source file with comments about the taintedness of the variables.";
    
       "-do-results", (* plug-in option *)
       Arg.Unit DoResultsEnabled.on,
       ": Compute a percentage of the tainted instructions.";
       
       "-print-vulnerable", 
       Arg.Unit PrintVulnerableSourceEnabled.on,
       ": Print the source file with comments for vulnerable function calls";
    
       "-do-prepare-slice",
       Arg.Unit PrepareSliceEnabled.on,
       ": Print a source file prepared for slicing for vulnerable statements";
    
       "-do-min-read-metrics",
       Arg.Unit MinReadMetricEnabled.on,
       ": Computes the best min read metrics path";
    
       "-do-max-read-metrics",
       Arg.Unit MaxReadMetricEnabled.on,
       ": Computes the best max read metrics path";    
    
       "-do-min-taint-metrics",
       Arg.Unit MinTaintMetricEnabled.on,
       ": Computes the best min taint metrics path";  
    
       "-do-max-taint-metrics",
       Arg.Unit MaxTaintMetricEnabled.on,
       ": Computes the best max taint metrics path";  
    
       "-taint-debug", (* plug-in option *)
       Arg.Unit Debugging.on,
       ": Turn debugging ON."; 
    
       "-taint-info", (* plug-in option *)
       Arg.Unit Info.on,
       ": Turn info ON.";
    
      (* TESTING *)
      "-do-ptranal",
       Arg.Unit PtranalEnabled.on,
       ": Computes points to analysis"; 
    
       "-config-file",
       Arg.String (Cmdline.Dynamic.Apply.String.set (option_config_file () )),
       ": The config file used for setting the entry point and annotating functions";
    
       "-constr-config-file",
       Arg.String (Cmdline.Dynamic.Apply.String.set (option_constr_config_file () )),
       ": The constraint config file containing the constraints that must be met by the called functions.";
       
       "-main-function",
       Arg.String (Cmdline.Dynamic.Apply.String.set (option_main_function () )),
       ": The name of the main function for considering command line arguments as tainted.";] 

(* Extend the Frama-C entry point (the "main" of Frama-C). *)
let () = Db.Main.extend run 
