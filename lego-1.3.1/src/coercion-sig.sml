
signature COERCION =
  sig
(* These are the functions called from elsewhere in the LEGO system to
   attempt to find and apply a coercion to some value.
   
   They take a current meta-variable substitution, and a source value
   together with it's type, and if successful return the coerced value
   and an updated substitution.

   The argument flavour of coercion requires a target type to which
   the value is to be coerced as an extra input. The pi and kind flavours
   return as an extra output the type of the coerced value returned.
 *) 
    val arg_co : (substitution * cnstr * cnstr * cnstr)
     -> (cnstr * substitution) option
    val kind_co : (substitution * cnstr * cnstr)
     -> (cnstr * substitution * cnstr) option
    val pi_co : (substitution * cnstr * cnstr)
     -> (cnstr * substitution * cnstr) option

(* The function for adding a new edge to the coercive graph. *)
    val add_paths : ((cnstr * cnstr * string * coercionFlavour) * paths) -> paths

(* Functions for changing or viewing all or some of the paths
   generated in the coercive graph.
 *)
    val get_paths : unit -> paths
    val get_paths_to : cnstr -> paths
    val get_paths_from : cnstr -> paths
    val get_paths_between : cnstr * cnstr -> paths
    val set_paths : paths -> unit

(* These are not needed outside the coercion module but are useful
   for debugging purposes.
 *)
    val matches : substitution * (cnstr * cnstr) list
     -> (substitution * param_subs) option
    val matches2 : (cnstr * cnstr) list -> param_subs option
  end;
