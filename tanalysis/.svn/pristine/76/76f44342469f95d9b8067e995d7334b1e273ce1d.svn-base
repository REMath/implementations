open TaintGamma

module Printer(Param:sig
                        val fmt : Format.formatter  
                        val debug : bool
                        val info : bool
                     end) = struct
    
    include Printer.Printer(struct 
                             let fmt = Param.fmt
                             let debug = Param.debug
                             let info = Param.info 
                            end)
    
    let print_taint () = Gamma.pretty_print_taint Param.fmt
    
    let print_env () = Gamma.pretty_print Param.fmt
    
    let print_taint_list () = Gamma.pretty_print_taint_list Param.fmt

    let print_taint_debug () taint = 
        if Param.debug then 
            print_taint () taint
        else
            Format.ifprintf Param.fmt "%s" "\n"
            
    let print_taint_info () taint =
        if Param.info then
            print_taint () taint
        else
            Format.ifprintf Param.fmt "%s" "\n"
            
    let print_env_debug () env = 
        if Param.debug then 
            print_env () env
        else
            Format.ifprintf Param.fmt "%s" "\n"
    
    let print_env_info () env =
        if Param.info then
            print_env () env
        else
            Format.ifprintf Param.fmt "%s" "\n" 
    
    let print_taint_list_debug () taint_list = 
        if Param.debug then 
            print_taint_list () taint_list
        else
            Format.ifprintf Param.fmt "%s" "\n"
    
    let print_taint_list_info () taint_list =
        if Param.info then
            print_taint_list () taint_list
        else
            Format.ifprintf Param.fmt "%s" "\n"
end
