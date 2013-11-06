local
    type 'a binder  = bindSort * visSort * frzLocGlob * string list * string list * 'a
    type  'a ctxt = 'a binder list
in
signature TOP =
    sig
	type cnstr_c
	val init_newtop : unit -> unit
	val Dnf : unit -> unit
	val V_Dnf : unit -> unit
	val T_Dnf : unit -> unit
	val Normal : unit -> unit
	val V_Normal : unit -> unit
	val T_Normal : unit -> unit
	val Hnf : 'a -> unit
	val V_Hnf : 'a -> unit
	val T_Hnf : 'a -> unit
	val Equiv : cnstr_c -> unit
	val V_Equiv : cnstr_c -> unit
	val T_Equiv : cnstr_c -> unit
	val Expand : int list -> string list -> unit
	val V_Expand : int list -> string list -> unit
	val T_Expand : int list -> string list -> unit
	val ExpAll : int list -> int -> unit
	val V_ExpAll : int list -> int -> unit
	val T_ExpAll : int list -> int -> unit
	val EvalCxt 
	    : (bindSort * visSort * (freeze * LocGlob) * string list * string list
	       * cnstr_c) list
	    -> unit
	val StartTimer : unit -> unit
	val PrintTimer : unit -> unit
	val legopath : unit -> string list
	val Eval : cnstr_c -> unit
	val EvalRed : cnstr_c -> unit

	(* inductive types *)
	type ind_options 
	val inductive_datatype : cnstr_c ctxt -> ind_options -> unit
	val record_type : cnstr_c ctxt -> ind_options -> unit
	val inductive_no_switches : ind_options
	val inductive_update_constructors : cnstr_c ctxt -> ind_options -> ind_options
	val inductive_update_params : cnstr_c ctxt -> ind_options -> ind_options
	val inductive_update_universe : cnstr_c -> ind_options -> ind_options
	val inductive_update_noreds : ind_options -> ind_options
	val inductive_update_double : ind_options -> ind_options
	val inductive_update_unsafe : ind_options -> ind_options
	val inductive_update_theorems : ind_options -> ind_options
	val inductive_update_relation : ind_options -> ind_options
	val inductive_update_inversion : ind_options -> ind_options
    end
end;
