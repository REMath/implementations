module Printer(Param:sig
                        val fmt : Format.formatter  
                        val debug : bool
                        val info : bool
                     end) = struct
                        
    let print () = Format.fprintf Param.fmt

    let print_debug () =
        if Param.debug then
            print ()
        else
            Format.ifprintf Param.fmt
            
    let print_info () =
        if Param.info then
            print ()
        else
            Format.ifprintf Param.fmt           
end
