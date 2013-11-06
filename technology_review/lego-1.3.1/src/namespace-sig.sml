(* 
   $Log: namespace-sig.sml,v $
   Revision 1.6  1998/11/10 15:30:00  ctm
   added interface for adding Labels and searching by corresponding tags

   Revision 1.5  1997/11/24 11:01:36  tms
   merged immed-may-fail with main branch

   Revision 1.4.2.3  1997/10/13 16:47:13  djs
   More problems with the above.

   Revision 1.4.2.2  1997/10/13 16:21:30  djs
   Because CVS charmingly breaks code by inserting the wrong comment
   markers.
  
   Revision 1.4.2.1  1997/10/10 17:02:39  djs
   Made everything work on Solaris, by taking out some nested comments.
  
   Revision 1.4  1997/05/08 13:54:59  tms
   Generalised Expansion Mechanism to Cope with Path information
  
   Revision 1.3  1997/03/06 09:54:00  tms
   added mkNameLoc and initNameLoc, previously available in the module pbp
*)

local
  type context=binding list
in
  signature NAMESPACE =
    sig
      datatype question =
	Push of int * int * cnstr
      | Unknown of assignment list;

      val init_namespace : unit -> unit
(*****************************************************************)
(* WARNING: These are UNSAFE; putNamespace must not be exported  *)
(*          putNamespace is currently required in toplevel.sml   *)
(*	                   discharge.sml, newtop.sml and         *)
(*                         build.sml (for debugging help)        *)
(*****************************************************************)
      val getNamespace  : unit -> context
      val putNamespace  : context -> unit

      val search        : string -> context -> binding
      val extendCxt     : Kind -> bindVisSort -> frzLocGlob -> string list
	-> string -> cnstr*cnstr
	-> context -> context
      val extendCxtGbl  : Kind -> bindVisSort -> frzLocGlob -> string list
	-> string -> cnstr * cnstr -> context
      val isNewName     : string -> bool
      val defined       : string -> context -> bool

      val mkNameGbl     : string -> string
      (*  mkNameGbl s = s if s is a fresh identifier relative to the context 
          mkNameGbl s = t for a fresh t otherwise *)

      val mkNameLoc     : string -> string
      (* mkNameLoc s = s if (mkNameGbl s = s) and s hasn't been returned
                            previously by mkNameLoc
	 mkNameLoc s = t for a fresh t otherwise
		
         Notice that initNameLoc will effectively undo any previous
         mkNameLoc invokation *)
      val initNameLoc   : unit -> unit
	  
      val latestTsGbl   : unit -> int
      val DischargeKeep : string -> unit
      val Discharge     : string -> unit
      val dischCxt 
	: cnstr * cnstr -> context
	-> (cnstr * cnstr) * binding * context
      val dischCxtGbl   : cnstr * cnstr -> (cnstr * cnstr) * binding
      val DECH          : unit -> unit
      val Forget        : string -> unit
      val addMark       : string*string list*time -> unit
      val addConfig     : string*string*string*string->unit
      val findConfig    : string->(string*string*string)->
                                  (string*string*string)
      val addLabel      : string list*string -> unit
      val spotLabel     : string list -> (cnstr*cnstr) option
      val init_history  : unit -> unit
      val pushHist      : unit -> unit
      val tacticalPushHist      : unit -> unit
      val pushHistProven: (string * LocGlob) * (cnstr * cnstr) -> unit
      val activeProofState : unit -> bool
      val proofState : unit -> bool
      val provenState   : unit -> bool
      val no_history    : (unit -> unit) -> unit -> unit
      val undo          : unit -> unit
      val discard       : unit -> unit
      val tactic_wrapper : (unit -> unit) -> unit -> unit
      val lclGen        : cnstr * cnstr -> string -> cnstr * cnstr
      val prt_context_dpth : int -> dfnsPrnt -> unit
      val prt_context_ref : binding -> dfnsPrnt -> unit
      val prt_context_nam : string -> dfnsPrnt -> unit
      val getNUN : unit -> int
      val Goal : cnstr -> unit;
      val getCurrentGoals  : unit -> question list
      val putCurrentGoals  : question list -> unit
      (******************************************************************)
      (* WARNING: This is UNSAFE; putCurrentGoals must not be exported  *)
      (*          putCurrentGoals is currently required in toplevel.sml *)
      (******************************************************************)
      val goals : unit -> substitution * question list
      val subgoals : unit
	-> (int * cnstr) * substitution * question list
      val Addq : substitution -> question list -> question list
      val erase_replace : substitution -> int -> substitution
	-> substitution -> substitution
      val eraseq : substitution -> question list -> question list
      val erase : substitution -> substitution
	-> substitution
      val manageVars : unit
	-> ((cnstr -> cnstr) *
	    (substitution -> assignment list) *
	    (unit -> int))
      val getContextBeforeProof : unit -> context

      val getProofTerm : unit -> cnstr
      val putProofTerm : cnstr -> unit
      (***************************************************************)
      (* WARNING: This is UNSAFE; putProofTerm must not be exported  *)
      (*          putProofTerm is currently required in toplevel.sml *)
      (***************************************************************)

      val Claim : cnstr -> substitution -> (cnstr -> cnstr) 
	-> (substitution -> assignment list) -> (unit -> int)
	-> unit
      val NextTac : int -> unit
      val do_intros : int -> string list -> bool * bool -> int
      val Save : string -> frzLocGlob -> unit
      val splitCtxt
	: (binding -> bool) -> string -> context -> binding * context * context
      val Dnf : unit -> unit
      val Normal : unit -> unit
      val Hnf : unit -> unit
      val Equiv : substitution -> cnstr -> int
      val Expand : int list -> string list -> unit
      val ExpAll : int list -> int -> unit
      val SaveReductGbl : cnstr * cnstr -> unit
      val makeAllPats : unit -> unit
      val killRef : unit -> unit
      val Undo : int -> unit
      val ForgetMrk : string -> unit
      val Freeze : string list -> unit
      val Unfreeze : string list -> unit
      val sub_Ref_pr
	: (int * cnstr) list -> cnstr * cnstr -> (cnstr * cnstr) modif
      val subRef : (int * cnstr) list -> cnstr -> cnstr
      val StartTheory : string -> unit
      val EndTheory : string -> unit
    end
end
