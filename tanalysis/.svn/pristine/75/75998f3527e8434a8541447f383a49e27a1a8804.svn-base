open Cil
open Cil_types
open Lexing
open VulnerableUtils

module VulnerablePrinter (Param:sig
                    val vulnerable_statements : vulnerability list
                    val fmt : Format.formatter
                    val debug : bool      
                    val info : bool     
                 end)=struct
  module P = Printer.Printer(struct
                                let fmt = Param.fmt
                                let debug = Param.debug
                                let info = Param.info
                              end)
                              
  let print () = 
    List.iter 
      (fun vulnerability ->
        match vulnerability with
        | FunctionConstraint (s, fname) -> 
            (match extract_loc s with 
            | Some loc ->
              P.print () 
                  "[%s:%i] Vulnerability: Function constraint doesn't hold for function '%s'\n" 
                  loc.pos_fname 
                  loc.pos_lnum fname
            | None -> ignore ()
            )
        | BufferIndex (s, bufname) -> 
            (match extract_loc s with 
            | Some loc ->
              P.print () 
                  "[%s:%i] Vulnerability: Buffer write with tainted index for buffer '%s'\n" 
                  loc.pos_fname 
                  loc.pos_lnum
                  bufname
            | None -> ignore ()
            ))
      Param.vulnerable_statements
end

let print vulnerable_statements fmt debug info =
  let module VP = VulnerablePrinter(struct 
                                      let vulnerable_statements = vulnerable_statements
                                      let fmt = fmt
                                      let debug = debug
                                      let info = info
                                    end) in
  VP.print ()
