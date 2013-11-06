(*
   $Log: newtop.sml,v $
   Revision 1.5  1998/11/10 15:31:08  ctm
   Inductive definitions Label themselves

   Revision 1.4  1997/11/24 11:01:43  tms
   merged immed-may-fail with main branch

   Revision 1.3.2.3  1997/10/13 16:47:15  djs
   More problems with the above.

   Revision 1.3.2.2  1997/10/13 16:21:35  djs
   Because CVS charmingly breaks code by inserting the wrong comment
   markers.
  
   Revision 1.3.2.1  1997/10/10 17:02:43  djs
   Made everything work on Solaris, by taking out some nested comments.
  
   Revision 1.3  1997/06/20 14:51:36  djs
   More changes to facilitate script management. Mostly to do with the
   protocol for annotations, but also changed the behaviour of lego wrt
   multiple declarations - now, if one fails, the others are rolled back.
  
   Revision 1.2  1997/05/08 13:56:05  tms
   Generalised Expansion Mechanism to Cope with Path information
*)

functor FunTop (structure Toplevel:TOPLEVEL
		structure Concrete:CONCRETE
		structure Namespace:NAMESPACE
		structure Synt:SYNT
		structure Inductive:INDUCTIVE
		structure Record:RECORD
		structure Double:DOUBLE
		structure Relation:RELATION
		structure Theorems:THEOREMS
		structure ConorInductive:CONORINDUCTIVE
		structure Type:TYPE
                sharing type Toplevel.cnstr_c=Concrete.cnstr_c and
			type Synt.cnstr_c=Concrete.cnstr_c and
			type Relation.cnstr_c=Inductive.cnstr_c and
			type Double.cnstr_c=Relation.cnstr_c and
			type Theorems.cnstr_c=Double.cnstr_c and
			type Double.cnstr_c=Concrete.cnstr_c and
			type Record.cnstr_c=Concrete.cnstr_c)
    : TOP  =
    struct
	local
	    open Synt  open Namespace
	in
	    type cnstr_c = Concrete.cnstr_c

	    (* scratch registers *)
val VAL = ref Prop
val TYP = ref (Type((uconst 0)));

fun init_newtop() = (VAL:= Prop; TYP:= Type((uconst 0)));


(** Reductions on subgoal, !VAL, !TYP **)

fun Dnf () =
    (Namespace.Dnf();
     message "DNF";
     Toplevel.Pr())

fun V_Dnf () = (VAL:=(dnf (!VAL)); legoprint (!VAL));
fun T_Dnf () = (TYP:=(dnf (!TYP)); legoprint (!TYP));

fun Normal () =
    (Namespace.Normal();
     message "Normalize";
     Toplevel.Pr())

fun V_Normal () = (VAL:=(UMnorm (!VAL)); legoprint (!VAL)); 
fun T_Normal () = (TYP:=(UMnorm (!TYP)); legoprint (!TYP));

fun Hnf n = (Namespace.Hnf(); message "HNF"; Toplevel.Pr()) 
fun V_Hnf n = (VAL:= UMwhnf (!VAL); legoprint (!VAL));
fun T_Hnf n = (TYP:= UMwhnf (!TYP); legoprint (!TYP));

fun Equiv trm_c =
    let
      val (mkVar,eraseNew,close) = manageVars()
      val ((V,_),sbst) = Concrete.EvalRefine type_of_Var mkVar trm_c
    in
	(Namespace.Equiv sbst V; message"Equiv"; Toplevel.Pr())
    end;

local
  fun tst (r:cnstr ref) (new:Concrete.cnstr_c) =
    let val (V,_) = Concrete.fEval new
    in  if par_tm V (!r) then (r:= V; message"true")
	else message"false"
    end
in
  val V_Equiv = tst VAL
  val T_Equiv = tst TYP
end;

fun Expand path nams = (Namespace.Expand path nams;
			print_words ("Expand"::nams
				     @["relative","to","the","path",
				       ListFormat.formatList
				       {init="[",sep=",",final="]",
					fmt=makestring} path]);
			Toplevel.Pr())

fun RegisterExpand register path nams =
    (register := dnf (foldl (C (fn s => Type.subtermApp path (Type.expand s)))
		      (!register) nams);
     legoprint (!register));

fun V_Expand path nams = RegisterExpand VAL path nams

fun T_Expand path nams = RegisterExpand TYP path nams

fun ExpAll path m = (Namespace.ExpAll path m;
		     print_words ("ExpAll "^string_of_num m::
				  ["relative","to","the","path",
				   ListFormat.formatList
				       {init="[",sep=",",final="]",
					fmt=makestring} path]);
		     Toplevel.Pr())

fun RegisterExpAll register path n =
    (register := (*dnf*) (Type.subtermApp path (Type.expAll n) (!register));
     legoprint (!register));

fun V_ExpAll path n = RegisterExpAll VAL path n
fun T_ExpAll path n = RegisterExpAll TYP path n


(* Evaluate contexts, unwrap on failure *)
fun EvalCxt cxt =
  let
    fun evalCxt (b,v,frz_par_flg,deps,ns,c) = 
      let
	fun ec n = extendCxtGbl Bnd (b,v) frz_par_flg deps n (Concrete.fEval c)
      in case v
	   of Def => (do_list ec ns;
		      prnt_defn (concat_sep " " ns)
		                (ref_val (hd (getNamespace())))
				(ref_typ (hd (getNamespace()))))
	    | _ => if activeProofState()
		     then failwith"Cannot add assumptions during a proof"
		   else (do_list ec ns;
			 prnt_decl v (concat_sep " " ns)
			             (ref_typ (hd (getNamespace()))))
      end
    val t = start_timer()
    val sn = getNamespace ()
    val _ = (do_list evalCxt cxt handle e => (putNamespace sn; raise e))
  in   message("  (* "^(makestring_timer t)^" *)")
  end;


local
  val t = ref (start_timer())
in
  fun StartTimer() = (t:= start_timer(); message"- Start Timer -")
  fun PrintTimer() = message("- Print Timer -  "^(makestring_timer (!t)))
end


(***  For dynamic changes to LEGOPATH ***)

local
  fun splitup([],l) = [implode (rev ("/"::l))]
    | splitup(":"::t, l) = (implode (rev ("/"::l))) :: (splitup(t,[]))
    | splitup(c::t, l) = splitup(t, c::l)
  val addPath = ref ([]:string list)
  val delPath = ref ([]:string list)
in
  fun legopath() =
    let
      fun check [] = ["./"]
	| check (h::t) =
	  if size h < 10 then check t
	  else case substring(h,0,9)
		 of "LEGOPATH=" =>
		   splitup (explode (substring(h,9,size h - 9)), [])
		  | _ => check t
    in
      check (System.environ())
    end
end;


fun Eval c =
  let
      val (v,t) = fst (Concrete.EvalRefine
		       type_of_Var (Concrete.parser_var_pack()) c)
    val nam = (case v
		 of (Ref br) => if ref_isDefnNow br
				  then (ref_nam br)
				else ""
		  | _ => "")
    val _ = VAL:= (case v of (Ref br) => ref_val br | _ => v)
    val _ = TYP:= t
  in
      print_value nam (!VAL);
      print_type  nam (!TYP)
  end;

fun EvalRed reduc =
  if activeProofState()
    then failwith"Cannot add reductions during a proof"
  else
    let
      val fEred = Concrete.fEval reduc
      val _ = SaveReductGbl fEred
      val _ = (prnt_red (fst fEred); message"compiling reductions")
    in makeAllPats()
    end

type 'a binder  = bindSort * visSort * frzLocGlob * string list * string list * 'a
type  'a ctxt = 'a binder list

type ind_options =
  {params:cnstr_c ctxt, constructors:cnstr_c ctxt, elimOver:cnstr_c,
   safe:bool, noReds:bool, double:bool, relation:bool,
   theorems: bool, inversion: bool};

    fun inductive_datatype ct2 indopt =
        let
          val oldcontext = getNamespace()
          val
    	{params=p,constructors=c,elimOver=e,
    	 safe=s,noReds=nr,double=d,relation=r,theorems=t,
             inversion=i} = indopt
          val nr = nr orelse c=[]
          val do_inductive_type =
                if d then Double.do_inductive_type_double
    		     else if r then Relation.do_weak_inductive_type
    					else Inductive.do_old_inductive_type
          val (ctxt1,reduc) = do_inductive_type s p ct2 c nr e
    	          handle Inductive.sch_err s => failwith ("Inductive: "^s)
          (* Claire's Theorems
          val ctxt2 = if t then (Theorems.do_just_theorems p ct2 c) else []
                  handle Theorems.sch_err s => failwith ("Theorems: "^s) *)
          (* stuff for picking out names of types being defined *)
          fun type_names [] = []
    	    | type_names ((_,_,_,_,l,_)::t) = l@(type_names t)
          val tns = type_names ct2
          fun bungInTypeLabel s = ((addLabel ([s],s));
                                   (addLabel ([s,"elim"],s^"_elim")))
          fun bungInConLabel c =
              let val (_,t) = Concrete.fEval (Concrete.Ref_c c)
                  fun ty (Bind ((Pi,_),_,_,r)) = ty r
                    | ty (App ((f,_),_)) = ty f
                    | ty (Ref b) = ref_nam b
                    | ty _ = bug "bad constructor type slipped through"
              in  addLabel ([ty t,c],c)
              end
        in
          ((EvalCxt ctxt1);
           (map bungInTypeLabel tns);
           (map bungInConLabel (type_names c));
           (if not nr then EvalRed reduc else ());
    	   (* Claire's Theorems  (if t then EvalCxt ctxt2 else ()); *)
    (* Conor's stuff goes here *)
           (if t then ((map ConorInductive.DoConorTheorems tns);()) else ());
           (if i then ((map ConorInductive.DoConorInversion tns);()) else ()))
          handle ex => (putNamespace oldcontext; raise ex)
        end;

fun record_type ct2 indopt = 
    let 
      val oldcontext = getNamespace()
      val
	{params=p,constructors=c,elimOver=e,
	 safe=s,noReds=nr,double=d,relation=r,theorems=t,
             inversion=i} = indopt 
      val (ctxt1,reduc,ctxt2) = Record.do_record_type p ct2 c e
                     handle Record.sch_err s => failwith ("Inductive: "^s);
    in
      ((EvalCxt ctxt1;
	(*       legoprint (fst (Parser.fEval reduc)); this looks like a bug *)
	EvalRed reduc;
       EvalCxt ctxt2)
      handle ex => (putNamespace oldcontext; raise ex))
    end

val inductive_no_switches = {params=([]:cnstr_c ctxt), constructors=([]:cnstr_c ctxt), 
			     elimOver=Concrete.Ref_c"TYPE", safe=true, noReds=false,
			     double=false,
			     relation=false, theorems=false, inversion=false }

    fun inductive_update_constructors constr
        {elimOver=e,safe=u,noReds=nr,double=d,params=p,relation=r,
         theorems=t,constructors=_,inversion=i}
        = {params=p,constructors=constr,elimOver=e,safe=u,noReds=nr,
           double=d,relation=r,theorems=t,inversion=i}
    
    fun inductive_update_params ctxt
        {constructors=c,elimOver=e,safe=u,noReds=nr,double=d,relation=r,
         theorems=t,params=_,inversion=i}
        = {params=ctxt,constructors=c,elimOver=e,safe=u,noReds=nr,
           double=d,relation=r,theorems=t,inversion=i}
    
    fun inductive_update_universe universe 
        ({safe=u,noReds=nr,double=d,params=p,relation=r,theorems=t,
          constructors=c,elimOver=_,inversion=i}:ind_options)
        = ({params=p,constructors=c,elimOver=universe,safe=u,
    	noReds=nr,double=d,relation=r,
        theorems=t,inversion=i}:ind_options)
    
    fun inductive_update_noreds
        {elimOver=e,safe=u,double=d,params=p,relation=r,theorems=t,
         constructors=c,noReds=_,inversion=i}
        = {params=p,constructors=c,elimOver=e,safe=u,noReds=true,
         double=d,relation=r,theorems=t,inversion=i}
    
    fun inductive_update_double
        {elimOver=e,safe=u,params=p,relation=r,theorems=t,constructors=c,
         noReds=nr,double=_,inversion=i}
        = {params=p,constructors=c,elimOver=e,safe=u,noReds=nr,
           double=true,relation=r,theorems=t,inversion=i}
    
    fun inductive_update_unsafe
        {elimOver=e,params=p,constructors=c,noReds=nr,double=d,
         relation=r,theorems=t,safe=_,inversion=i}
        = {params=p,constructors=c,elimOver=e,safe=false,noReds=nr,
           double=d,relation=r,theorems=t,inversion=i}
    
    fun inductive_update_theorems
        {elimOver=e,params=p,constructors=c,noReds=nr,double=d,
         relation=r,safe=u,theorems=_,inversion=i}
        = {params=p,constructors=c,elimOver=e,safe=u,noReds=nr,double=d,
           theorems=true,relation=r,inversion=i}
    
    fun inductive_update_relation
        {elimOver=e,params=p,constructors=c,noReds=nr,double=d,
         theorems=t,safe=u,relation=_,inversion=i}
        = {params=p,constructors=c,elimOver=e,safe=false,noReds=nr,
           double=d,relation=true,theorems=t,inversion=i}
    
    fun inductive_update_inversion
        {elimOver=e,params=p,constructors=c,noReds=nr,double=d,
         theorems=t,safe=u,relation=r,inversion=_}
        = {params=p,constructors=c,elimOver=e,safe=false,noReds=nr,
           double=d,relation=r,theorems=t,inversion=true}

end
end
