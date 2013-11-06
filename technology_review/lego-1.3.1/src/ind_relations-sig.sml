local
    type 'a binder = bindSort * visSort * frzLocGlob * string list * string list * 'a
    type 'a ctxt   = 'a binder list
in
    signature INDUCTIVE =
	sig
	    exception sch_err of string
	    type cnstr_c

	    (* schema_head is not just a string, but a string
	     applied to some arguments.... *)
	    datatype schema_head =
		Head of string |
		Appl_a of prntVisSort * schema_head * cnstr_c;

	    (* This is a variant on the concrete syntax cnstr_c
with account taken of schema variables *)
		
	    datatype schema_c =
		Ref_s of schema_head  (* A schema variable *)
	      | Bind_s of cnstr_c binder * schema_c  (* Simple binding (x:K) where
						K is not a schema *)
	      | Bind_sc of schema_c binder * schema_c  (* Complex binding by a schema *)
	    val binders_ind : cnstr_c -> (string * cnstr_c * visSort) list
	    val start_T_of_C : (string * 'a * visSort) list -> string -> cnstr_c
	    val arities : schema_c -> (string * visSort * schema_c) list
	    val binders : schema_c -> (string * visSort * cnstr_c) list
	    val gen_app : cnstr_c -> visSort -> string list -> cnstr_c
	    val get_name_app : schema_head -> string
	    val get_name_and_type : schema_c -> string * schema_head
	    val iota_of_a : string * schema_c -> cnstr_c
	    val pr_cc : 'a -> unit
	    val eliminators
		: (string * cnstr_c) list
	        -> (string * schema_c) list -> cnstr_c
		-> cnstr_c ctxt
	    val third_bindings : ('a * schema_c) list -> cnstr_c ctxt
	    val get_names : cnstr_c ctxt -> string list
	    val recursor_applied_to_bindings
		: (string * 'a) list -> (string * 'b) list -> 'c * schema_c -> cnstr_c
	    val make_name_list 
		: (cnstr_c binder) list
		-> cnstr_c ctxt
		-> (string * cnstr_c) list
	    val subst_c : string * string -> cnstr_c -> cnstr_c
	    val redo_bindings_with_dependency
		: bool -> cnstr_c ctxt -> cnstr_c ctxt -> cnstr_c ctxt -> cnstr_c ctxt
	    val make_disj_var_schemas : ('a * schema_c) list -> ('a * schema_c) list
	    val make_schema_list : cnstr_c binder list -> cnstr_c binder list -> (string * schema_c) list
	    val nice_schemas : ('a * schema_c) list -> ('a * schema_c) list
	    val make_reductions 
		: (string * cnstr_c) list -> (string * schema_c) list -> cnstr_c -> cnstr_c
	    val do_old_inductive_type : bool -> cnstr_c ctxt -> cnstr_c ctxt 
                                          -> cnstr_c ctxt -> bool -> cnstr_c 
                                            -> cnstr_c ctxt * cnstr_c

	end
end
