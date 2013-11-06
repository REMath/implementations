local
  type 'a binder =
    bindSort * visSort * frzLocGlob * string list * string list * 'a
  type 'a ctxt = 'a binder list
in
  signature CONCRETE =
    sig
      datatype cnstr_c =
	Prop_c
      | Theory_c
      | Type_c of string
      | TypeAbs_c of int
      | Ref_c  of string
      | App_c  of prntVisSort * cnstr_c * cnstr_c
      | Bind_c of cnstr_c binder * cnstr_c
      | Tuple_c of (cnstr_c list) * cnstr_c
      | Proj_c of projSort * cnstr_c
      | Ctxt_c of cnstr_c ctxt * cnstr_c
      | Cast_c of cnstr_c * cnstr_c
      | wCast_c of cnstr_c * cnstr
      | Case_c of cnstr_c * (cnstr_c ctxt * cnstr_c * cnstr_c) list
      | Red_c of cnstr_c ctxt * ((cnstr_c*cnstr_c) list)
      | Var_c  of int  (* metavars for use in refinements *)
      | NewVar_c       (* make a new metavar *)
      | Normal_c of cnstr_c
      | Hnf_c of int * cnstr_c
      | Dnf_c of cnstr_c
      | RedTyp_c of instrs * cnstr_c
      | TypeOf_c of cnstr_c
      | Gen_c of cnstr_c * string
      | Bot_c
      val unEval : cnstr -> cnstr_c
      val fEvalCxt : binding list -> cnstr_c -> cnstr * cnstr
      val fEval : cnstr_c -> cnstr * cnstr
      val parser_var_pack : unit -> cnstr -> cnstr
      val EvalRefine : (int -> cnstr)
	-> (cnstr -> cnstr) -> cnstr_c
	-> (cnstr * cnstr) * substitution
    end
end
