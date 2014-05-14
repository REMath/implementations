(* 
   $Log: namespace.sml,v $
   Revision 1.14  1998/11/10 15:30:48  ctm
   added code for adding Labels and searching by corresponding tags;
   modified Discharge to cope with `Generate' and `Label'

   Revision 1.13  1998/10/30 14:15:55  ctm
   discharge modified to take visibility from resulting abstractions etc,
   rather than the initial binding---allowing for conditional visibility

   Revision 1.12  1998/10/28 16:01:45  ctm
   Modified discharge so parameter visibilities are chosen according to
   argument type dependency; eg list and nil have visible type arg while
   cons and list_elim suppress it.

   Revision 1.11  1998/10/23 13:50:52  tms
   "Forget id" now also reports on retraction across module boundaries.
   This is required for the Emacs interface Proof General

   Revision 1.10  1998/10/18 11:35:50  tms
   Function forget now prints out a loud message. This makes it easier
   for an interface such as Proof General to recognise that LEGO has
   retracted across file boundaries.

   Revision 1.9  1997/11/24 11:01:39  tms
   merged immed-may-fail with main branch

   Revision 1.8.2.2  1997/10/13 16:21:33  djs
   Because CVS charmingly breaks code by inserting the wrong comment
   markers.

   Revision 1.8.2.1  1997/10/10 17:02:41  djs
   Made everything work on Solaris, by taking out some nested comments.
  
   Revision 1.8  1997/05/08 13:55:07  tms
   Generalised Expansion Mechanism to Cope with Path information
  
   Revision 1.7  1997/03/06 09:54:09  tms
   added mkNameLoc and initNameLoc, previously available in the module pbp
*)

val Dep_debug = ref false;

functor FunNamespace(structure Machine:MACHINE
		     structure UndoKnots:CONORKNOTS
                     structure Infix: INFIX
		     structure Type: TYPE
		     sharing UndoKnots.KT = UndoKnotTypes)
   : NAMESPACE  =
struct
  type cnstr=cnstr
  type context = binding list;

  (* "quest" is the type of the current goals.
   * Empty is the null list of subgoals.
   * Push indicates introductions, hence a change of context.
   *    When Push is the head of a "quest", a discharge is
   *    needed, after Push is removed so previous goals are
   *    restored in their correct context.
   * Unknown is the list of subgoals in the current context.
   *)
  datatype question =
    Push of int * int * cnstr
  | Unknown of assignment list;
  type quest = question list;

  (* history; for UNDO *)
  datatype hist = Initial
  | NoProof
  | State of state
  | Proven of ((string*LocGlob) * (cnstr*cnstr)) * hist
  withtype state =
    cnstr * quest * int * context * univ_graph * hist;

  (* for gensym *)
  val NUN = ref(0);

  fun getNUN () = !NUN (* we can work out if tacs create new goals this way *)

  val NSP = ref([]: context);
  fun latestTsGbl() = ref_ts (hd (!NSP));

  (* local namespace with constructors initNameLoc and mkNameLoc *)
  val LNSP = ref ([]:string list)

  (* la preuve partielle *)
  val COM = ref Bot;
  fun getProofTerm() = (!COM)
  fun putProofTerm t = COM := t

  local
    fun ff s (m,c) l = if mem_assoc m s then l else (m,sub s c)::l
  in
    fun erase_replace s n new =
      let fun fff (m,c) l = if n=m then new@l else ff s (m,c) l
      in  foldr fff []
      end
    fun erase s = foldr (ff s) []
  end;

  (* some tools for managing metavars *)
  fun manageVars() =
    let 
      val nun = ref(!NUN)
      val newVars = ref([] : assignment list)
      fun mkVar cc = 
	let val nc = ((nun:= !nun+1; !nun),cc) 
	in (newVars:= !newVars@[nc]; Var(nc))
	end
      fun eraseNewVars t = 
	(newVars:= map (fn (n,c) => (n,dnf c)) (erase t (!newVars));
	 !newVars)
      fun closeNewVars() = (NUN:= !nun; !NUN)
    in  (mkVar,eraseNewVars,closeNewVars)
    end;

  fun Addq l =
    if l=[] then I
    else fn Unknown(l1)::q => Unknown(l@l1)::q     (* add new subgoals *)
  | q              => Unknown(l)::q;


  (* reference to newest context before proof *)
  val GOAL_CTXT = ref (!NSP);
  fun getContextBeforeProof() = (!GOAL_CTXT)

  val QUEST = ref([] : quest);
  fun getCurrentGoals() = (!QUEST)
  fun putCurrentGoals g = QUEST := g

(* Sorry about this---hopefully it's only a temporary inconvenience... *)

(* Conor notes...
Three things:

(1) We need the ability to suppress Undo marking, so that tactics composed
     from other tactics only leave one mark. Hence the wrapper tactical
     no_history, crudely implemented here in a reentrant fashion.
(2) Tacticals which work by backtracking need to make their own (non-user)
     Undo marks. They should do this with tacticalPushHist. Any such mark
     should be removed without fail, either with undo (if backtracking is
     necessary) or with discard (if it isn't)---discard throws away the
     mark without affecting the proof. This should ensure that the only
     marks which survive between user commands are user Undo marks.
(3) There is now a facility for attaching other structures to the history
     mechanism on an ad hoc basis---this is principally to support the
     Then tactical. Any such additional structure requires methods for
     "Init" (run at start of proof), "Mark" (run by pushHist), "Undo"
     (one step) and "Discard" (one step).
*)

	val HIST = ref NoProof;
	val HIST_HACK = ref 0;
        fun markEnabled () = (!HIST_HACK) >= 0
	fun init_history() = (HIST := NoProof;
			   (map (fn f => f ())
			    (UndoKnots.seek_all_knots (fn f => f="Init")));())
	fun pushHist() = if (markEnabled ())
		     then ((* message "pushHist"); *)
                           (HIST:= State(!COM,!QUEST,!NUN,!NSP,!UVARS,!HIST));
(* run Mark methods *)     (map (fn f => f ())
			    (UndoKnots.seek_all_knots (fn f => f="Mark")));())
			 else ()
	fun tacticalPushHist() = (* must be undone or discarded *)
	    ((* (message "tacticalPushHist");*)
	     (HIST:= State(!COM,!QUEST,!NUN,!NSP,!UVARS,!HIST));
	     (map (fn f => f ())
	      (UndoKnots.seek_all_knots (fn f => f="Mark")));())
	fun pushHistProven nvt = HIST:= Proven(nvt,!HIST)
	fun proofState() = !HIST <> NoProof
	fun no_history tac () =
	    ((HIST_HACK := ((!HIST_HACK)-1));
	    (tac ());
	    (HIST_HACK := ((!HIST_HACK)+1)))
	    handle x => ((HIST_HACK := ((!HIST_HACK)+1)); raise x)

(*  val HIST = ref NoProof;
  fun init_history() = HIST := NoProof

  fun pushHist() = HIST:= State(!COM,!QUEST,!NUN,!NSP,!UVARS,!HIST)
  fun pushHistProven nvt = HIST:= Proven(nvt,!HIST)
  fun proofState() = !HIST <> NoProof *)

  fun activeProofState() =
    case !HIST of Initial => true | State s => true | _ => false

  fun provenState() = case !HIST of Proven s => true | _ => false;

  fun goals() = if activeProofState()
		  then case (getCurrentGoals())
			 of Unknown(l)::q => (l,q)
			  | _             => bug"goals"
		else failwith"no current goals"

  fun subgoals() = case goals()
		     of ((nc as (n,c))::l,q) => (nc,l,q)
		      | ([],_)               => bug"subgoals"

  fun Claim v sbst mkVar eraseNew close =
    let
      val (l,q) = goals()
    in
      mkVar v; close();
      pushHist();
      QUEST := Unknown(l@(eraseNew sbst))::q
    end

  (* Interrogate the namespace *)
  fun search nam = 
    let fun fail() = failwith("search: undefined or out of context: "^nam)
      fun srec ((v as Bd{bd=(_,n,_,_),...})::l) =
	if n=nam then v
	else srec l
	| srec [] = fail()
    in srec
    end
		
  fun defined nam cxt = (search nam cxt; true) handle Failure _ => false;

  fun isNewName s = not (defined s (!NSP))

  (* make a name not occurring in the global context *)
  fun mkNameGbl nam = 
    let fun mnrec m =
      let val nn = nam^string_of_num m
      in if isNewName nn then nn else mnrec (succ m) end
    in if isNewName nam then nam else mnrec 1
    end;

  (* make a name neither occurring in the global nor in the local namespace *)
  fun mkNameLoc (s:string) =
      let
	  fun new_name _ = 
	      let val real_name = mkNameGbl s
	      in
		  if (member real_name (!LNSP)) then
		      let fun new_name_aux n  =
			  let val cur_s = (s ^ (makestring n))
			      val cur_real_name = mkNameGbl cur_s in
				  if member cur_real_name (!LNSP) then
				      new_name_aux (n + 1) 
				  else 
				      cur_real_name
			  end
		      in 
			  new_name_aux 0 
		      end
		  else real_name
	      end
	  val new_id = new_name()
      in
	  LNSP := new_id::(!LNSP); new_id
      end

  (* initialise local namespace *)
  fun initNameLoc _ = LNSP := []

  (* expand namespace *)
  fun Pure nam c =
    if (pure c) then true
    else failwith ("namespace: attempt to bind "^nam^" to impure term");


  fun extendCxt knd bv =
    let
      fun Assume bv (_,par_flg) deps nam (t,k) cxt =
	let val K = whnf k
	in if kind k (***** andalso Pure nam t *************)
	     then (Bd{ts=timestamp(),frz=ref UnFroz,
		      param=par_flg,deps=deps,kind=knd,
		      bd=(bv,nam,t,K)})::cxt
	   else (print_cannot_assume nam t K;
		 failwith "Only a Prop or a Type may be assumed")
	end
      fun Define bv (frz_flg,par_flg) deps nam (vt1,vt2) cxt =
	let
	  val _ = Pure nam vt1
	  val vt2 = dnf vt2
	in
	  (Bd{ts=timestamp(),frz=(ref frz_flg),param=par_flg,
	      deps=deps,kind=knd,bd=(bv,nam,vt1,vt2)})::cxt
	end
    in
      case bv
	of bv as (Let,Def) => Define bv
	 | (Let,_)         => bug"extendCxt:Let,_"
	 | (_,Def)         => bug"extendCxt:_,Def"
	 | bv              => Assume bv
    end
  fun extendCxtFresh K bv frz_par_flg deps n tk cxt =
    if isNewName n 
      then extendCxt K bv frz_par_flg deps n tk cxt
    else failwith("\""^n^"\" already in namespace")
  fun extendCxtGbl K bv frz_par_flg deps n tk = 
    (NSP:= extendCxtFresh K bv frz_par_flg deps n tk (!NSP); !NSP);


  fun eraseq s =
    let fun map_quest fU fc =
      map (fn Unknown(l) => Unknown(fU l) | Push(n,m,c) => Push(n,m,fc c))
    in  map_quest (erase s) (sub s)
    end

  (* on veut d'abord chercher une preuve du sous-but n *)
  fun NextTac n =
    let fun reorder n ((u as (p,_))::l) = 
      if p=n then (u,l) 
      else let val (v,l') = reorder n l in (v,u::l') end
	  | reorder n [] = failwith("reorder: subgoal "^string_of_num n
				    ^" not found")
    in
      if n=(~9999) then ()
      else (QUEST:= let val (l,q) = goals() 
			val (u,l') = reorder n l
		    in  Unknown(u::l')::q
		    end;
	    ())
    end;

  local
    fun mk_goal c = ((NUN:= 1+(!NUN);!NUN),c)
    fun push_so_far ((n,c),l,q) h c' =
      if eq (c,c') then ()
      else let val gl = mk_goal c'
	   in  (QUEST:= Unknown([gl])::((Push(n,h,!COM))
					::(Addq l q));
		COM:= Var(gl); () )
	   end
    fun mk_name nam s = mkNameGbl(if nam<>"" then nam
				  else if s<>"" then s else "H")
  in
    fun do_intros count lst (flgs as (hnfFlg,autoFlg)) =
      let
	fun intros_rec count lst c push =
	  let
	    fun pi_intro nam nams ((_,vis),s,c1,c2) push =
	      let
		val nam = mk_name nam s
		val newCxt =
		  extendCxtGbl Bnd
		  (Lda,vis) (UnFroz,Local) [] nam (c1,type_of_constr c1)
	      in
		intros_rec (count+1) nams (subst1 (Ref(hd newCxt)) c2) push
	      end
	    fun sig_intro (sigBod as (_,s,tl,tr)) =
	      let
		val ((n,c),l,q) = subgoals()
		val goal_l = mk_goal tl
		val tr = subst1 (Var goal_l) tr
		val goal_r = mk_goal tr
		(***********  Tuple is unsafe ********)
		val sbst = [(n,Tuple(Bind sigBod,[Var goal_l,Var goal_r]))]
	      in
		(QUEST:= eraseq sbst (Unknown(goal_l::goal_r::l)::q);
		 COM:= sub sbst (!COM); () )
	      end
	    fun let_intro nam nams ((_,vis),s,c1,c2) push =
	      let
		val nam = mk_name nam s
		val newCxt =
		  extendCxtGbl Bnd
		  (Let,vis) (UnFroz,Local) [] nam (c1,type_of_constr c1)
	      in  
		intros_rec (count+1) nams (subst1 (Ref(hd newCxt)) c2) push
	      end
	  in
	    case if autoFlg then [""] else lst
	      of "#"::nams => (case whnf c
				 of Bind(b as ((Sig,_),_,_,_)) =>
				   (push c; sig_intro b;
				    do_intros count nams flgs)
				  | _ => failwith"cannot do Sigma intro")
	       | nam::nams =>
		   (case if hnfFlg then whnf c else c
		      of Bind(b as ((Pi,_),_,_,_)) => pi_intro nam nams b push
		       | Bind(b as ((Sig,_),_,_,_)) =>
			   if autoFlg then (push c; sig_intro b;
					    do_intros count nams flgs)
			   else failwith("SIG Intro with improper token: "^nam)
		       | Bind (b as ((Let,_),_,l,r)) => let_intro nam nams b push
		       | _  => if autoFlg then (push c; count)
			       else failwith"goal has wrong form for intros")
	       | [] => (push c; count)
	  end
	val (sgs as ((_,c),_,_)) = subgoals() 
	val h = latestTsGbl()
      in
	intros_rec count lst c (push_so_far sgs h)
      end
  end;


  exception UndoExn

fun undo() =
  (let fun restore (c,q,n,v,u,h) =
    (COM:=c;QUEST:=q;NUN:=n;NSP:=v;UVARS:=u;HIST:=h;())
  in  case !HIST
	of State st => restore st
	 | Proven(_,State st) => restore st
	 | Initial => (NSP:= (!GOAL_CTXT); raise UndoExn)
	 | _ => bug"undo"
  end;(map (fn f => f ()) (UndoKnots.seek_all_knots (fn f => f="Undo")));
  (*(message "undo");*)())

fun discard() = (* Throws away history mark, but not proof *)
  (let fun restore (c,q,n,v,u,h) =
    (HIST:=h;())
  in  case !HIST
	of State st => restore st
	 | Proven(nvt,State st) => ((restore st);(pushHistProven nvt))
	 | Initial => (NSP:= (!GOAL_CTXT); raise UndoExn)
	 | _ => bug"discard"
  end;(map (fn f => f ()) (UndoKnots.seek_all_knots (fn f => f="Discard")));
  (*(message "discard");*)())

(********************************************************************)
(* tactic_wrapper ensures that the tactic it wraps obeys:           *)
(* (1) successful tactics mark history if enabled, then change      *)
(*       the state                                                  *)
(* (2) failing tactics neither mark history nor change state        *)
(********************************************************************)

fun tactic_wrapper f () =
    ( (tacticalPushHist());
      (no_history f ());
      (if (markEnabled()) then () else discard ()) )
    handle x => ((undo());(raise x))

(******************************************************)
(* WARNING: These are UNSAFE;                         *)
(*          put is currently required in toplevel.sml *)
(******************************************************)
fun getNamespace() =  (!NSP)
fun putNamespace nsp = NSP := nsp

fun curnt_bndng_ref() = hd (!NSP);


fun init_namespace() = NSP:=[Bd{ts=timestamp(),
				frz=ref UnFroz,
				param=Global,
				deps=[],
				kind=Bnd,
				bd=((Pi,Vis),"** Start of Context **",
				    Prop,Type (uconst 0))}];


(* freezing and unfreezing *)
fun Freeze ns =
  let fun freeze n = let val br = search n (!NSP)
		     in  (ref_frz br):= Froz
		     end
  in  do_list freeze ns
  end
fun Unfreeze ns =
  let
    fun unf br = (ref_frz br):= UnFroz
    fun unfreeze n = let val br = search n (!NSP)
		     in  unf br
		     end
  in  if ns = [] then do_list unf (!NSP)
      else do_list unfreeze ns
  end
		
		
(* reductions in Contexts *)
fun SaveReductGbl VT =
  let fun saveReduct (v,t) cxt =
    (Bd{ts=timestamp(),frz=ref UnFroz,param=Global,deps=[],kind=Red,
	bd=((Sig,VBot),"",v,t)})::cxt
  in NSP:= saveReduct VT (!NSP)
  end;
fun makeAllPats() =     (* where to put this? *)
  let fun addRed (Bd{bd=(_,_,v,_),kind=Red,...}) = add_reductions v
	| addRed _ = ()
  in (init_reductions(); do_list addRed (rev (!NSP)))
  end;


(* Return the latest timestamp in the Global context *)

fun prt_context_dpth n elideFlg = 
  let
    val lnsp = length (!NSP)
    val real_n = if n>lnsp then lnsp else n

  in
    if n <= 0 then ()
    else do_list (print_ctxt elideFlg) (rev (first_n real_n (!NSP)))	 
  end;

local
  fun depth f m = fn b::rest => if f b then m else depth f (m+1) rest
| []      => m
in fun prt_context_ref br elideFlg =
  prt_context_dpth (depth (fn b => sameRef b br) 0 (!NSP)) elideFlg
   fun prt_context_nam nam elideFlg =
     prt_context_dpth (depth (fn b => sameNam b nam) 1 (!NSP)) elideFlg
end;


(* DEEP dependency of a subject ref on an object ref *)
fun DEPENDS skip br_obj br_sbj =
  let
    val nam = ref_nam br_obj
    fun Depends c =  (* DEEP dependency of a term on a name *)
    case c
      of (Ref br) =>
	(if (!Dep_debug)
	   then message("**Dep "^nam^" "^ref_nam br^" "^
			concat_sep " " (map ref_nam skip))
	 else ();
	 DEPENDS skip br_obj br)
       | (App((c,cs),_)) => (Depends c) orelse (exists Depends cs)
       | (Bind(_,_,c,d)) => (Depends d) orelse (Depends c)
       | (Tuple(T,l))    => (Depends T) orelse (exists Depends l) 
       | (CnLst l)       => exists Depends l
       | (Proj(_,c))     => Depends c
       | (RedTyp(_,c))   => Depends c
       | (Var(_,c))      => Depends c
       | _               => false
  in
    (not (exists (sameRef br_sbj) skip)) andalso
    ref_ts br_obj <= ref_ts br_sbj andalso
    (if (!Dep_debug)
       then message("**DEP "^nam^" "^ref_nam br_sbj^" "^
		    concat_sep " " (map ref_nam skip))
     else ();
     sameRef br_sbj br_obj orelse
     let val (v,t) = ref_vt br_sbj
     in  Depends v orelse Depends t
     end orelse
       exists (DEPENDS (br_sbj::skip) br_obj)
           (map (fn n => search n (!NSP)) (ref_deps br_sbj)))    (** ??? **)
  end;

(* split context when property pred becomes true *)
fun splitCtxt pred msg cxt = 
  let
    fun sr pre (br::brs) = if pred br then (br,pre,brs)
			   else sr (br::pre) brs
      | sr pre []        = failwith msg
  in
    sr [] cxt
  end;

local   (* substitutions of *closed* terms for Ref's (by timestamp) *)
  fun sub_Ref s = 
    let
      fun sub_rec (Ref br)  = (Mod(assoc (ref_ts br) s) handle Assoc => UMod)
	| sub_rec (Var b)   = mkVar sub_rec b
	| sub_rec (App b)   = mkApp sub_rec b
	| sub_rec (Bind b)  = mkBind2 sub_rec b
	| sub_rec (Tuple b) = mkTuple sub_rec b
	| sub_rec (CnLst b) = mkCnLst sub_rec b
	| sub_rec (Proj b)  = mkProj sub_rec b
	| sub_rec (RedTyp b) = mkRedTyp sub_rec b
	| sub_rec (LabVT b) = mkLabVT sub_rec b
	| sub_rec _         = UMod
    in sub_rec
    end
in
  fun sub_Ref_pr s = share2 (sub_Ref s,sub_Ref s)  (** type cnstr modif **)
  fun subRef s = share (sub_Ref s)
  fun subRef_pr s = share (sub_Ref_pr s)
end;

val disch_debug = ref false

fun dischCxt VT =
  let
    fun preDischCxt br =
      case ref_bind br
	of Let => Machine.letize VT br
	 | Lda => Machine.abstract VT br
	 | Pi => Machine.generalize VT br
	 | Sig => Machine.sigize VT br
	 | Thry => bug"dischCxt"
  in
    fn  b::bs  => (preDischCxt b,b,bs)
     | []      => failwith"cannot discharge; context empty"
  end

fun dischCxtGbl VT = let val (vt,b,bs) = dischCxt VT (!NSP)
		     in  (NSP:= bs; (vt,b))
		     end;

(* ye olde version *******************************************************)
(* should work fine with new ? binder---the clever bit is now in Machine *)
(* except that we need to get the prVis after the oper is run            *)
local
  fun spotVis (Bind ((_,v),_,_,_)) = prVis v
    | spotVis _ = ShowForce
  fun dk (left,deltas,moved) br =
    let
      val _ = (prs(" "^ref_nam br); flush_out std_out)
      fun discharge oper deps (vt as (v,t)) br_sbj =
	let
	  val _ = if !disch_debug
		    then (prs("\n** disch debug **  ");
			  prnt_vt v t)
		  else ()
	  (* we must remove a ref from deps once it is discharged *)
	  fun operate (vcvd as (vt as (v,t),cs,vs,deps)) br =
	    (if !disch_debug
	       then (prs("\n**operate** "^ref_nam br^", "); prnt_vt v t)
	     else ();
	       if (depends br v orelse depends br t orelse
		   (exists (DEPENDS [br_sbj] br)
		    (map (fn nam => search nam (!NSP)) deps)))
		 then case ref_bind br
			of Lda => let val vt as (v,t) = oper vt br
                                  in (* need to get vis after oper *)
                                  (vt,
				   (Ref br)::cs,
				   (spotVis v)::vs,
				   filter_neg (sameNam br) deps)
                                  end
			 | Let => (Machine.letize vt br,cs,vs,
				   filter_neg (sameNam br) deps)
			 | _ => bug"funny Discharge"
	       else vcvd)
	in 
	  foldl operate (vt,[],[],deps) moved
	end
      fun globalDefn ts deps vt br_sbj =
	let
	  val (vt,cs,vs,ndeps) =
	    discharge Machine.abstract deps (subRef_pr deltas vt) br_sbj
	  val br' = ref_updat_vtdeps br vt ndeps
	in  
	  (br'::left,
	   compose subRef [(ts,MkApp((Ref br',cs),vs))] deltas,
	   moved)
	end
      fun globalDecl ts deps vt br_sbj =
	let	           (* a global decl depends on everything! *)
	  val (vt,cs,vs,ndeps) =
	    discharge Machine.generalize deps (subRef_pr deltas vt) br_sbj
	  val br' = ref_updat_vtdeps br vt ndeps
	in  
	  (br'::left,
	   compose subRef [(ts,MkApp((Ref br',cs),vs))] deltas,
	   moved)
	end
      fun reductions ts deps vt br_sbj =
	let
	  val (vt,cs,vs,ndeps) =
	    discharge Machine.abstract deps (subRef_pr deltas vt) br_sbj
	  val br' = ref_updat_vtdeps br vt ndeps
	in  
	  (br'::left,deltas,moved)
	end
      fun localDecl ts n vt =
	let
	  val vt = subRef_pr deltas vt
	  val br'= ref_updat_vt br vt
	in
	  (left,compose subRef [(ts,Ref br')] deltas,br'::moved)
	end
      fun localDefn ts n vt =
	let
	  val vt = subRef_pr deltas vt
	  val br'= ref_updat_vt br vt
	in
	  (left,compose subRef [(ts,Ref br')] deltas,br'::moved)
	end
    in
      case ref_body br of
	{kind=Bnd,ts,param=Global,deps=deps,bd=((Let,_),_,v,t),...} => 
	  globalDefn ts deps (v,t) br
      | {kind=Bnd,ts,param=Global,deps=deps,bd=(_,_,v,t),...} =>
	  globalDecl ts deps (v,t) br
      | {kind=Bnd,ts,param=Local,bd=((Let,_),n,v,t),...} =>
	  localDefn ts n (v,t)
      | {kind=Bnd,ts,param=Local,bd=(_,n,v,t),...} =>
	  localDecl ts n (v,t)
      | {kind=GenTag _,ts,param=Global,deps=deps,bd=((Let,_),_,v,t),...} => 
	  globalDefn ts deps (v,t) br
      | {kind=GenTag _,ts,param=Global,deps=deps,bd=(_,_,v,t),...} =>
	  globalDecl ts deps (v,t) br
      | {kind=GenTag _,ts,param=Local,bd=((Let,_),n,v,t),...} =>
	  localDefn ts n (v,t)
      | {kind=GenTag _,ts,param=Local,bd=(_,n,v,t),...} =>
	  localDecl ts n (v,t)
      | {kind=Red,ts,deps=deps,bd=(_,_,v,t),...} =>
	  reductions ts deps (v,t) br
      | {kind=Mrk(_),...} => (br::left, deltas, moved)
      | {kind=Config(_),...} => (br::left, deltas, moved)
      | {kind=LabelTag _,...} => (br::left, deltas, moved)
      | _ => bug"dk"
    end
in
  fun dischg nam msg =
    if activeProofState() then failwith"No Discharge in proof state"
    else let
	   val  t = start_timer()
	   val (hit,new,old) =
                splitCtxt (fn br => sameNam br nam) (nam^" undefined") (!NSP)
	   val _ = prs("Discharge and "^msg^".. ")
	   val _ = init_history()
	   val res = foldl dk (old,[],[]) (hit::new)
	   val _ = message("\n   (* "^(makestring_timer t)^" *)")
         in  res
	 end
end;

local
  fun dischState nsp = (NSP:= nsp; line(); makeAllPats())
in
  fun DischargeKeep nam = let val (left,_,moved) = dischg nam "keep"
			  in  dischState (moved@left)
			  end
  and Discharge nam = let val (left,_,_) = dischg nam "forget"
		      in  dischState left
		      end
end;

fun DECH() =
  let 
    fun disCom m VT =
      let
	fun dc VT =
	  if m<>latestTsGbl()
	    then let val (VT,br) = dischCxtGbl VT
		 in  (prs(" "^ref_nam br); dc VT) 
		 end
	  else (fst VT)
      in 
	if m<>latestTsGbl()
	  then (prs "Discharge.. "; let val V = dc VT in line(); V end)
	else fst VT
      end
  in
    case (!QUEST) of
      Unknown([])::q => QUEST := q
    | Push(n,m,c)::q =>
	let val com = !COM
	    val sbst = [(n,disCom m (com,type_of_constr com))]
	in  COM := sub sbst c;
	    QUEST := eraseq sbst q
	end
    | [] => COM:= disCom (ref_ts (hd(!GOAL_CTXT))) (!COM,type_of_constr (!COM))
    | _  => bug "Namespace.DECH"
			 
  end
				 
fun Goal v = (GOAL_CTXT := !NSP;
	      NUN := 0;
	      QUEST := [Unknown[(0,v)]];
	      COM := Var(0,v);
	      HIST := Initial)
    
fun Undo n = repeat n undo () handle UndoExn => ()

fun killRef() =
  let fun undoAll() = (Undo 9999999; init_history())
  in
    if activeProofState()
      then (message"Warning: forgetting an unfinished proof"; undoAll())
    else if provenState()
      then (message"Warning: forgetting a finished proof"; undoAll())
    else()
  end


local
  fun forget f nopMsg killMsg smsg =
    let
      val _ = splitCtxt f nopMsg (getNamespace())  (* to see if nam is there *)
      val _ = killRef()                            (* Forget forces Kill *)
      fun sr (br::brs) = 
	  (case br of 
	       Bd{kind=Config("Infix",b,c,d),...} => 
		   (Infix.infix_forget b; sr brs)
	     | _ => if f br then brs else sr brs)
	| sr []        = failwith killMsg        
    in  (NSP:= sr (getNamespace()); makeAllPats(); smsg())
    end

fun ForgotMark mrk = "forgot back through Mark \""^mrk^"\""
in
  fun Forget nam =
      let
	  (*** The interface (Proof General) would like to know when
	  we retract across module boundaries. We therefore keep track 
	  of module boundary in the context. ***)
	  val module = ref NONE
      in
	  forget (fn br => if (ref_isMrk br)
			       then (module := SOME (ref_mrk br); false)
			   else sameNam br nam)
	  ("Forget is no-op; \""^nam^"\" not in namespace")
	  ("Forget forced KillRef; \""^nam^"\" no longer in namespace")
	  (fn () =>
	   ((case !module of
	       NONE => ()
	     | SOME mrk => loudmessage (ForgotMark mrk));
		message ("forgot back through "^nam)))
      end
  fun ForgetMrk mrk =
    forget (fn br => sameMrk br mrk)
           ("ForgetMark is no-op; \""^mrk^"\" not in namespace")
	   ("bug at ForgetMark")
	   (fn () => loudmessage ( ForgotMark mrk))
end;

fun addLabel tn =
    NSP := (Bd{ts=timestamp(),frz=ref UnFroz,param=Global,
	deps=[],kind=LabelTag tn,bd=((Sig,VBot),"",Bot,Bot)})::(!NSP)

fun spotLabel tag =
      let fun gotB b = if ref_isBnd b then SOME (Ref b,ref_typ b) else NONE
          fun s2 [] = NONE
            | s2 (b::t) = let val k = ref_kind b
                          in  case k
                                of LabelTag (tag',id) =>
				   if tag=tag'
                                   then gotB (search id (!NSP))
                                        handle _ => NONE
                                   else s2 t
                                 | GenTag tag' => if tag=tag'
                                                  then gotB b
                                                  else s2 t
                                 | _ => s2 t
                          end
      in  s2 (!NSP)
      end

fun addConfig config
    = NSP:= (Bd{ts=timestamp(),frz=ref UnFroz,param=Global,
		deps=[],kind=Config config,bd=((Sig,VBot),"",Bot,Bot)})::(!NSP)

    fun findConfig key fail =
        let
            fun fc2 [] = fail
              | fc2 ((Bd{kind=Config(a,b,c,d),...})::tail) =
                if (a=key) then (b,c,d) else fc2 tail
              | fc2 (_::tail) = fc2 tail
        in
            fc2 (!NSP)
        end

fun addMark (m,i,t)
    = NSP:= (Bd{ts=timestamp(),frz=ref UnFroz,param=Global,
		deps=[],kind=Mrk(m,i,t,start_timer()),
		bd=((Sig,VBot),"",Bot,Bot)})::(!NSP)

fun lclGen vt backto =
    let
	fun dch (vt as (v,t)) br =
	    if (depends br v) orelse (depends br t)
		then case ref_bind br
		    of Let => Machine.letize vt br
		  | Lda => Machine.abstract vt br
		  | _ => bug"funny Gen"
	    else vt
	fun step vt =
	    fn br::rmndr => let val nvt = dch vt br
			    in  if sameNam br backto then nvt
				else step nvt rmndr
			    end
	     | [] => failwith(backto^" undefined or out of scope") 
    in 
	step vt (!NSP)
    end
(***********
fun readable nams =
  let
    fun nams_brs nams = map (fn s => search s (!NSP)) nams
    fun insert br brs = if member br brs then brs else br::brs
    fun close br targ =
      if depends br targ then
      else if same_ref targ br then 
  in
  end;
****************)

fun Save name (frz_lg as (frz_flg,locGlob)) =
  case !HIST
    of Proven(((n,lg),vt),_) =>
      let                             (*  Save line vs Goal line! *)
	val name =
	  case (n,name)
	    of ("","") => failwith("cannot Save: no name provided")
	     | (x,"") => x
	     | ("",x) => x
	     | (x,y) => if x=y then x
			else failwith("cannot Save: two names provided: \""^
				      n^"\" and \""^name^"\"")
	val locGlob = (case (lg,locGlob)       (* as Local as possible *)
			 of (Global,Global) => Global
			  | _ => Local)
      in
	(extendCxtGbl Bnd (Let,Def) frz_lg [] name vt;
	 (init_history ());
	 message ("\""^name^"\"  saved as "^
		  (if locGlob=Local then "local, " else "global, ")^
		  (if frz_flg=Froz then "frozen" else "unfrozen")))
      end
     | NoProof => failwith"no proof to save"
     | _ => failwith("cannot Save \""^name^"\": proof unfinished")

fun Dnf() = let val ((n,c),l,q) = subgoals()
		val q' = (Unknown((n,dnf c)::l))::q
	    in (pushHist();
		QUEST:= q')
	    end

fun Normal () =
    let val ((n,c),l,q) = subgoals()
        val q' = (Unknown((n,UMnorm c)::l))::q
        in (pushHist();
            QUEST:= q') end;

fun Hnf n =
    let val ((n,c),l,q) = subgoals()
        val q' = (Unknown((n,UMwhnf c)::l))::q
        in (pushHist();
            QUEST:= q') end;

fun Equiv (sbst:substitution) (V:cnstr) =
    let
	val (mkVar,eraseNew,close) = manageVars()
	val ((nc as (n,c)),l,q) = subgoals()
    in
      case par_unif sbst V c of
	SOME(s) =>
	  let val newT = sub s V
	      val new = (n,newT)::(eraseNew s)
	  in (pushHist();
	      QUEST:= Unknown(erase_replace s n new (nc::l))::(eraseq s q);
          (*  COM:= sub [(n,LabVT(StrongCast,Var(n,newT),c))] (!COM);  *)
	      close())
	  end
      | NONE => failwith"not convertible"
    end

fun Expand path nams =
    let val ((n,c),l,q) = subgoals()
    in  (pushHist();
         QUEST:= (Unknown((n,dnf (foldl (C (fn s => Type.subtermApp path (Type.expand s))) c nams))::l))::q)
    end;

fun ExpAll path m =
    let val ((n,c),l,q) = subgoals()
    in  (pushHist();
         QUEST:= (Unknown((n,dnf (Type.subtermApp path (Type.expAll m) c))::l))::q)
    end;

(************ theory packaging **************)

(* Mark the start of theory "nam" *)
fun StartTheory nam =
  let
    fun addThry() = NSP := (Bd{kind=StThry nam,
			       ts=timestamp(),
			       frz=ref UnFroz,
			       param=Global,
			       deps=[],
			       bd=((Sig,VBot),"",Bot,Bot)})::(!NSP)
    val _ = if activeProofState()
	      then failwith"Cannot start a theory in proof state"
	    else ()
    val _ = if defined nam (!NSP)
	      then failwith("Name \""^nam^"\" already in namespace")
	    else ()
    val _ = message("Starting theory \""^nam^"\"")
  in
    addThry()
  end;
fun EndTheory nam =
  let
    local
      fun sub_Ref s = 
	let fun sub_rec n =
	  fn (Ref br)  => (Mod(assoc (ref_ts br) s n) handle Assoc => UMod)
	   | (Var b)   => mkVar (sub_rec n) b
	   | (App b)   => mkApp (sub_rec n) b
	   | (Bind b)  => mkBind sub_rec n b
	   | (Tuple b) => mkTuple (sub_rec n) b
	   | (CnLst b) => mkCnLst (sub_rec n) b
	   | (Proj b)  => mkProj (sub_rec n) b
	   | (RedTyp b)=> mkRedTyp (sub_rec n) b
	   | (LabVT b) => mkLabVT (sub_rec n) b
	   | _         => UMod
	in sub_rec 1
	end
    in
      fun osubRef s = share (sub_Ref s)
    end
    val _ = if activeProofState()
	      then failwith"No \"EndTheory\" in proof state"
	    else ()
    val (_,newbrs,oldbrs) =
      splitCtxt (fn br => ref_stThry br = SOME nam) (nam^" undefined") (!NSP)
    val _ = prs("Package theory named \""^nam^"\": ")
    fun pack (br::brs) sbst lvts =
      let
	val rnbr = ref_nam br
      in
	if not (ref_isDefn br)   (****  allow decls and frozen  *****)
	  then (message"";
		failwith("Attempt to pack a non-definition, \""^
			 rnbr^"\", in theory "^nam^"\"."))
	else let
	       val _ = prs(" "^rnbr)
	       val lvt = MkLabVT(Name rnbr,
				 (* improve sharing by using VT pair *)
				 osubRef sbst (ref_VAL br),
				 osubRef sbst (ref_TYP br))
	       (* don't have to compose sbsts in this special case *)
	       val nsbst = (ref_ts br,fn m => Proj(Labl rnbr,Rel m))::sbst
	     in
	       pack brs nsbst (lvt::lvts)
	     end
      end
	 | pack [] _ lvts = lvts
    val lvts =  rev (pack newbrs [] [])
    val _ = prs"\n"
    val thry = Bind((Thry,VBot),"",Theory,CnLst lvts)
    val _ =
      NSP:= extendCxtFresh Bnd (Let,Def)
                           (UnFroz,Global) [] nam (thry,Theory) oldbrs
  in  ()
  end

end
