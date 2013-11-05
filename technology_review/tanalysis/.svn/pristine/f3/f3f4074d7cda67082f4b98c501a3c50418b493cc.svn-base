(*test*)
open Cil_types

module AliasAnalysis(Param:sig
                        val fmt : Format.formatter
                        val debug : bool
                        val info : bool
                    end) = struct
    
            
    module P = Printer.Printer(struct 
                                let fmt = Param.fmt
                                let debug = Param.debug
                                let info = Param.info 
                                end)

    let get_aliases vinfo =
        P.print_info () "[INFO] Returning alias for %s: %s.\n TODO: Not implemented yet.\n" vinfo.vname vinfo.vname;
        [vinfo]
end
 
