local
    type 'a binder  = bindSort * visSort * frzLocGlob * string list * string list * 'a
    type  'a ctxt = 'a binder list
in
    signature RECORD =
	sig
	    exception sch_err of string
	    type cnstr_c
	    val do_record_type : cnstr_c ctxt -> cnstr_c ctxt -> cnstr_c ctxt -> cnstr_c 
                                   -> cnstr_c ctxt * cnstr_c * cnstr_c ctxt
	end
end;
