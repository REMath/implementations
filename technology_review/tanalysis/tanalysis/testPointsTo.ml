open Cil_types
open Cilutil
open Cil
open Visitor

class visitor = object (self)

    inherit Visitor.generic_frama_c_visitor 
        (Project.current ()) (inplace_visit ()) as super

    method vlval lval =
      (match lval with 
      | (Var vinfo, _) -> 
        Format.printf "May Aliases for %s: [" vinfo.vname;
        List.iter 
          (fun a_vinfo ->
            Format.printf "%s " a_vinfo.vname)
          (Ptranal.resolve_lval lval);
        Format.printf "%s\n" "]"
      | _ -> ignore ());
      DoChildren
      
    initializer 
      Ptranal.analyze_file (Cil_state.file ())
end