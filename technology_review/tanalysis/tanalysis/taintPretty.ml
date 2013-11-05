open Cil
open Cil_types
open TaintGamma

class print func_envs = object(self)
    inherit defaultCilPrinterClass as super

    method private getDifferences stmt_envs env s =
        let old_envs = 
            List.map
                (fun pred -> Inthash.find stmt_envs pred.sid)
                s.preds in
        let result_env = 
            Gamma.get_differences env old_envs in
        (Gamma.env_length result_env > 0, result_env)

    method private pDifferences fmt env stmt=
        super#pGlobal fmt (GText "");
        super#pGlobal fmt (GText (Format.sprintf "/*sid:%d*/" stmt.sid));
        Gamma.env_iter
            (fun vid taint ->
                let str_taint = Gamma.pretty_string_taint vid taint in
                super#pGlobal fmt (GText (Format.sprintf "/*%s*/" str_taint)))
            env

    method pAnnotatedStmt next fmt s =
        let current_func_vinfo = self#current_function in
        match current_func_vinfo with
            | None ->
                assert(false)
            | Some vinfo ->
                try 
			        let (_, stmt_envs) = Inthash.find func_envs vinfo.vid in
	                let env = Inthash.find stmt_envs s.sid in
	                let (has_diff, result_env) = self#getDifferences stmt_envs env s in
                    super#pGlobal fmt (GText (Format.sprintf "/*sid:%d*/" s.sid)); 
	                match has_diff with
	                    | true ->
	                        super#pAnnotatedStmt next fmt s;
	                        self#pDifferences fmt result_env s
	                    | false ->
	                        super#pAnnotatedStmt next fmt s
                with
                    | Not_found ->
                        (* TODO: check what happens with extern variables *)
                        super#pGlobal fmt (GText "/* TODO: CHECK TAINT */");
                        super#pAnnotatedStmt next fmt s
    	
end