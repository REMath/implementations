(* discharge.sml *)

(** Commands to DISCHARGE an assumption; to FORGET assumptions;
 ** and to CUT an assumption to a particular witness 
 **)

functor FunDischarge (structure Namespace:NAMESPACE
		      structure Concrete:CONCRETE)
(*  : DISCHARGE *)
 =
struct
type cnstr_c = Concrete.cnstr_c
open Namespace

(* Cut: to specialize declarations *)
(* Ref's should have ts of their referent, NOT the value! *)
fun Cut cc =
  let
    fun unsplit_subRef s (new,old) =
      case new
	of (br::rest) =>
	  let val vt = ref_vt br
	      val (newbr,chg_flg) =
		case sub_Ref_pr s vt
		  of UMod => (br,false)
		   | (Mod vt') => (ref_updat_vt br vt',true)
	      val news = if chg_flg
			   then compose subRef [(ref_ts br,Ref newbr)] s
			 else s
	  in  unsplit_subRef news (rest,newbr::old)
	  end
	 | [] => old;
    fun cut cxt (lft,rht) =
      let
	val (rv,_) = Concrete.fEval rht
	val (hit,new,old) =
	  splitCtxt (fn br => sameNam br lft) (lft^" undefined") cxt
        fun expand_as_needed cxt =
	  fn (rbr as (Ref br)) =>
                    if ref_isDefn br andalso (not (defined (ref_nam br) cxt))
		      then (expand_as_needed cxt) (ref_VAL br) else rbr
	   | (App b) => umkApp (expand_as_needed cxt) b
	   | (Bind b) => umkBind2 (expand_as_needed cxt) b
	   | (Tuple b) => umkTuple (expand_as_needed cxt) b
	   | (CnLst b) => umkCnLst (expand_as_needed cxt) b
	   | (Proj b) => umkProj (expand_as_needed cxt) b
	   | (RedTyp b) => umkRedTyp (expand_as_needed cxt) b
	   | x         => x
	val (rv,rt) =
	  Concrete.fEvalCxt old (Concrete.unEval (expand_as_needed old rv))
	val (ts,param,deps,t) =
	  case hit
	    of Bd{ts,param,deps,bd=(_,_,t,_),...}
	      => if not (ref_isDecl hit)
		   then failwith("LHS of Cut is a definition: "^lft)
		 else if not (par_tm rt t)    (******  better msg *****)
		   then failwith("type does not match in Cut: "^lft)
		 else (ts,param,deps,t)
	val param = case param of Local => Global | Global => Local
	val cut_hit = Bd{kind=Bnd,ts=ts,frz=ref UnFroz,param=param,deps=deps,
			 bd=((Let,Def),lft,rv,t)}
      in (message("Cut "^lft);
	  unsplit_subRef [(ts,Ref cut_hit)] (new,cut_hit::old))
      end
  in putNamespace (foldl cut (getNamespace()) cc)
  end;

end
