local
    type 'a binder  = bindSort * visSort * frzLocGlob * string list * string list * 'a
    type  'a ctxt = 'a binder list
in
    signature THEOREMS =
	sig
	    exception sch_err of string
	    type cnstr_c
	    val do_just_theorems : cnstr_c ctxt -> cnstr_c ctxt -> cnstr_c ctxt
		                     -> cnstr_c ctxt
	end
end;
