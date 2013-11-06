local
    type context=binding list
in
    signature SYNT =
    sig
	type cnstr_c
	type question

	val type_of_Var : int -> cnstr
	
	val goaln : int -> int * cnstr
	val goal_rel : bool * int -> int * cnstr
	val resolve_c 
	    : int
	    -> int
	    -> cnstr_c
	    -> context * substitution * cnstr * question list
	    * (unit -> int) * cnstr
	val resolve_a 
	    : int
	    -> int
	    -> cnstr
	    -> context * substitution * cnstr * question list
	    * (unit -> int) * cnstr
    end
end
