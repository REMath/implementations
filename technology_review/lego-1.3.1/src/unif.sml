(* unif.ml *)

(* WARNING: In the future, if bindings can ever mention ex-vars then
 * many things in this file need to be re-thought.
 *)

val unif_debug = ref false;
val whun_debug = ref false;

(* iterative deepening parameters *)
val unif_start_dpth = ref  50;
val unif_deepen_factor = ref 2;

type assignment = int * cnstr;
type substitution = assignment list;

(** foward reference to par_tm **)
val r_par_tm = ref(fn x:cnstr => fn y:cnstr => false);

structure Unif : 
  sig
    val pure : cnstr -> bool
    val semi_pure : cnstr -> bool
    val sub : substitution -> cnstr -> cnstr
    val sub_pr : substitution -> cnstr * cnstr -> cnstr * cnstr
    val compose 
      : (substitution->cnstr->cnstr) -> substitution -> substitution -> 
      substitution
    val type_match_unif : substitution -> cnstr -> cnstr -> substitution option
    val whnf_unif : substitution -> cnstr -> cnstr -> substitution option
    val type_match_heur : cnstr -> cnstr -> bool
  end =
struct


(** existential variables: utilities, substitutions **)

(* pure c is true if c has no ex-variables *)
(* semi_pure c is true if c has no ex-vars unresolved from 
 * argument synthesis *)
(* mv_occur n c is true if Var(n,_) occurs in c *)
local 
  fun occ f = 
    let val rec occ_rec =
      fn Var(m,_) => f m
       | App((c,cs),vs) => (occ_rec c) andalso (for_all occ_rec cs)
       | try as Bind((Thry,_),_,c,d) =>
	   (if not (!theory_debug) then ()
	    else (prs"\n##thry_debug:occ in ";legoprint try);
	    (occ_rec c) andalso (occ_rec d))
       | Bind(_,_,c,d) => (occ_rec c) andalso (occ_rec d)
       | Tuple(T,ls)   => (occ_rec T) andalso (for_all occ_rec ls)  
       | CnLst(ls)     => for_all occ_rec ls
       | Proj(_,c)     => occ_rec c
       | RedTyp(_,c)   => occ_rec c
       | LabVT(_,v,_)  => (occ_rec v)
       | _             => true
    in occ_rec end
in 
  val pure = occ (fn m => false)
  val semi_pure = occ (fn m => m >= 0)
  fun mv_occur n = neg (occ (fn m => n<>m))
end;


(** ex-variable substitution **)

(* Apply a substitution to a construction *)
(* NOTE: we don't lift, so a substitution can have NO free
 * object-language variables.  This is enforced by reunion *)
fun sub [] = I
  | sub s  =  
    let
      fun sub_rec (Var(b as (n,t))) =
	   (Mod(assoc n s) handle _ => mkVar sub_rec b)
	| sub_rec (App b)   =  mkApp sub_rec b
	| sub_rec (try as Bind(b as ((Thry,_),_,_,_))) =
	  (if not (!theory_debug) then ()
	   else (prs"\n##thry_debug:sub in ";legoprint try);
	   mkBind2 sub_rec b)
	| sub_rec (Bind b)  =  mkBind2 sub_rec b
	| sub_rec (Tuple b) =  mkTuple sub_rec b
	| sub_rec (CnLst b) =  mkCnLst sub_rec b
	| sub_rec (Proj b)  =  mkProj sub_rec b
	| sub_rec (RedTyp b)=  mkRedTyp sub_rec b
	| sub_rec (LabVT b) =  mkLabVT sub_rec b
	| sub_rec _         =  UMod
    in share sub_rec end
fun sub_pr sbst (V,T) =
  let val sub_fun = sub sbst in (sub_fun V,sub_fun T) end;


(* compose a binding with a substitution *)
(** Warning: depends on 'sub' searching from head to tail
 ** because composite may have multiple bindings for a variable *)
fun compose sub (b:substitution) (s:substitution) : substitution = 
  case b
    of [(m,_)] => (map (fn (n,c) => (n,sub b c)) s) @ b
     | _ => bug"compose";


(** unification **)

exception Unif;     (* fail: different structure *)

(* uniflg=true for unification;
 * false for heuristic type matching (failing on any Var)
 *)
fun Unirec uniflg LMflg s (M,N) =
  let
    exception unif
    exception unifVar  (* fail: variable is found (heuristic type matching) *)
    val DpthExceeded = ref false

    fun unirec (Dpth as (dpth,maxd)) LMflg s (MN as (M,N)) =
      let
        fun debPrtDpth() = (makestring dpth)^" "^(makestring maxd)^" "^
                           (makestring (!DpthExceeded))^" "
 	fun raiseUnif (s,(m,n)) =
	  (if not (!unif_debug) then ()
	   else (message("**raiseUnif* "^debPrtDpth()^s);
                 print_expand m; print_expand n);
	   raise unif);
	val _ = if dpth<=maxd then ()
                else (DpthExceeded:= true; raiseUnif("dpth ",MN))
        fun handleUnif an = UVARS:= an

	fun reunion (p,P) M =
	  (* we guarantee that p is not bound in s, but M may be a meta-var.
	   * p and M may be the same meta-var, but that is not an occur check
	   *)
	  let
	    val ov = free_occur M
	    val mv = mv_occur p M
	  in
	    if mv orelse ov
	      then raiseUnif
		(("reunion: "^(if mv then "occurs check" else "free o-var")),
		 (Bot,Bot))
	    else let val tM = type_of_constr M
		     val s = Unirec uniflg (!LuosMode) s (tM,P)
                             handle Unif => raise unif
		 in compose sub [(p,M)] s
		 end
	  end

	fun uniargs s args1args2 = 
	  let fun uabod s mn = unirec (dpth+1,maxd) false s mn 
	  in  foldl uabod s (ListUtil.zip args1args2 handle _ => bug"uniargs")
	  end

	fun progWhnf c =     (* all the way to whnf *)
	  (if not(!unif_debug) then ()
	   else (prs"** unif_deb; whnf: "; legoprint c);
	     case rUMwhnf c of
	       UMod => raiseUnif("backtrack:no change on reduction",(Bot,Bot))
	     | Mod(c) => c)

	fun try_approx MN =
	  let
	    val MN as (M,N) = sub_pr s MN
	    val unifDfnFlgs = DF{beta=true,gdfn=true,ldfn=true,spdfn=true}
(********************************************
	    fun isName c =
	      case c of
		(Ref _) => true
	      | (Proj(_,b)) => isName b
	      | (App((f,_),_)) => isName f
	      | _ => false
********************************************)
	    fun eagerP x =  (* this is entirely heuristic: what is good
			     * to reduce more eagerly than definitions:
			     * higher numbers are more eager *)
	      case x of
		App((Bind((Lda,_),_,_,_),_),_) => 10
	      | Proj(Fst,Tuple _) => 10
	      | Proj(Snd,Tuple _) => 8
	      | Bind((Let,_),_,_,_) => 12
	      | _ => ~1                (*  neg means no eager contraction *)
	    local
	      fun ur mn = unirec (dpth+1,maxd) LMflg s mn
	      fun first flg stopTS =
		let
		  exception ta
		  fun exp1 tmplt c =
		    case s1UMwhbenf stopTS c
		      of Mod(c') => tmplt c'
		       | UMod => (case s1UMwhbenf ~1 c
				    of Mod(c') => tmplt c'
				     | UMod => raise ta)
		  fun expM() = exp1 (fn c => ur (c,N)) M
		  fun expN() = exp1 (fn c => ur (M,c)) N
		in
		  if flg then
		    let val _ = if !unif_debug
				  then message"**unif_debug: firstM"
				else ()
		    in  expM() handle ta =>
		        expN() handle ta =>
			raiseUnif("backtrack",MN)
		    end
		  else
		    let val _ = if !unif_debug
				  then message"**unif_debug: firstN"
				else ()
		    in  expN() handle ta =>
		        expM() handle ta =>
			raiseUnif("backtrack",MN)
		    end
		end
	    in
	      val firstM = first true
	      val firstN = first false
	      fun both() =
		case (s1UMwhbenf ~1 M,s1UMwhbenf ~1 N)
		  of (Mod M,Mod N) => ur (M,N)
		   | (Mod M,UMod) => ur (M,N)
		   | (UMod,Mod N) => ur (M,N)
		   | (UMod,UMod) => raiseUnif("backtrack",MN)
	    end
	    fun onlyM() = unirec (dpth+1,maxd) LMflg s (progWhnf M,N)
	    fun onlyN() = unirec (dpth+1,maxd) LMflg s (M,progWhnf N)
	  in
	    case (whnfP unifDfnFlgs M,whnfP unifDfnFlgs N)
	      of (true,true) => raiseUnif("backtrack: both are pwhnfs",MN)
	       | (false,true) => onlyM()   (* direct to whnf *)
	       | (true,false) => onlyN()   (* direct to whnf *)
	       | (false,false) =>
		   (case (eagerP M,eagerP N) of
		      (~1,~1) =>
			(case MN of
			   (App((Ref bM,_),_),App((Ref bN,_),_)) =>
			     let val tsM = ref_ts bM
			         val tsN = ref_ts bN
			     in  if tsM<tsN then firstN tsM
				 else firstM tsN
			     end
(****************************************
			 | (App((Ref bM,_),_),Ref bN) =>
			     let val tsM = ref_ts bM
			         val tsN = ref_ts bN
			     in  if tsM<tsN then firstN tsM else firstM tsN
			     end
			 | (Ref bM,App((Ref bN,_),_)) =>
			     let val tsM = ref_ts bM
			         val tsN = ref_ts bN
			     in  if tsM<tsN then firstN tsM else firstM tsN
			     end
************************************)
			 | _ => firstM ~1)
		    | (m,n) => if m>=n             (** expand both? **)
				 then firstM ~1 else firstN ~1)
	  end

	val MN as (M,N) =
	  let
	    fun clean c =
	      case c of
		RedTyp(_) => bug"unif;clean RedTyp"
	      | Bot => bug"unif;clean Bot"
	      | CnLst(_) => bug"unif;clean CnLst"
	      | LabVT(_) => bug"unif;clean LabVT"
	      | _ =>  c
	  in  (sub s (clean M),sub s (clean N))
	  end
	val _ = if not(!unif_debug) then ()
		else (prs("*unif_deb,  "^debPrtDpth());
		      message(" uniflg "^makestring uniflg);
		      prs"   ";print_expand M;
		      prs"   ";print_expand N)
      in
(*************************
(* if we're not already running par_tm, and M and N are pure, then
 * try par_tm locally
 *)
	if uniflg andalso pure M andalso pure N
	  then if !r_par_tm M N then s else raiseUnif("tm fails",MN)
	else
******************)
	case MN of
	  (Var(mtm as (m,_)),Var(ntn as (n,_))) =>
	    if m=n then s
	    else if not uniflg then raise unifVar
		 else if m>n then reunion mtm N
		      else reunion ntn M
	| (Var(mtm),_) => if uniflg then reunion mtm N else raise unifVar
	| (_,Var(ntn)) => if uniflg then reunion ntn M else raise unifVar
	| (Type(i),Type(j)) =>
	    if (if LMflg then univ_leq i j else univ_equal i j)
	      then s
	    else raiseUnif("Types",MN)
	| (Prop,Type(j)) => if LMflg then s else raiseUnif("Prop/Type",MN)
	| (Prop,Prop) => s
	| (Rel n,Rel m)  => if n=m then s else raiseUnif("Rel",MN)
	| (Rel m,N) =>
	    if varn_occur m N then unirec Dpth false s (M,progWhnf N)
	    else raiseUnif("Rel_Other",MN)
	| (M,Rel n) =>
	    if varn_occur n M then unirec Dpth false s (progWhnf M,N)
	    else raiseUnif("Other_Rel",MN)
	| (Ref b1,Ref b2) => (* since decls may expand by special,
			      * defns and decls are treated the same *)
	    if sameRef b1 b2 then s else try_approx MN
	| (Bind((Let,_),_,v1,b1),Bind((Let,_),_,v2,b2)) =>
	    let
	      fun expBoth() = 
		let
		  val v1 = sub s v1
		  val v2 = sub s v2
		in  unirec (dpth+1,maxd) false s (subst1 v1 b1,subst1 v2 b2)
		end
	      val an = !UVARS
	    in unirec (dpth+1,maxd) LMflg (unirec (dpth+1,maxd) false s (v1,v2)) (b1,b2)
	      handle unif => (handleUnif an; expBoth())
	    end
	    (****  special case: one redex and one non-redex **
			| (App m, App n) =>
			    let
			      val mn = (m,n)
fun intenApp (((f1,cs1),vs1),((f2,cs2),vs2)) =
	     let val an = !UVARS
  in  let
	val l1 = length cs1 and l2 = length cs2
val (f1,f2,cs1,cs2) =
	     if l1 = l2 then (f1,f2,cs1,cs2)
		  else if l1 < l2 
			 then let val l2l1 = l2-l1
				  val (pre,post) = chop_list l2l1 cs2
				  val (prev,postv) = chop_list l2l1 vs2
			      in  (f1,App((f2,pre),prev),cs1,post)
			      end
		       else let val l1l2 = l1-l2
				val (pre,post) = chop_list l1l2 cs1
				val (prev,postv) = chop_list l1l2 vs1
			    in  (App((f1,pre),prev),f2,post,cs2)
			    end
	      in uniargs (unirec (dpth+1,maxd) false s (f1,f2)) (cs1,cs2)
	      end                          (* in case of beta *)
	    handle unif => (handleUnif an;try_approx MN)
	  end
      in case mn of
	(((Bind((Lda,_),_,_,b1),c1::cs1),_),              (* two redexes *)
	 ((Bind((Lda,_),_,_,b2),c2::cs2),_)) => intenApp mn
      | (((Bind((Lda,_),_,_,b1),c1::cs1),_::vs1),_) =>    (* one redex only *)
	  unirec (dpth+1,maxd) LMflg s (App((subst1 c1 b1,cs1),vs1),N)
      | (_,((Bind((Lda,_),_,_,b2),c2::cs2),_::vs2)) =>
	  unirec (dpth+1,maxd) LMflg s (M,App((subst1 c2 b2,cs2),vs2))
      | _ => intenApp mn                                  (* no redex *)
      end
***********************)
(**********************
  | (App((f1,cs1),vs1),App((f2,cs2),vs2)) =>
      let
	fun fold s (c1::cs1,_::vs1,c2::cs2,_::vs2) =
	      fold (unirec (dpth+1,maxd) false s (c1,c2)) (cs1,vs1,cs2,vs2)
	  | fold s ([],[],[],[]) = unirec (dpth+1,maxd) false s (f1,f2)
	  | fold s (cs1,vs1,[],[]) =
	    (case (f1,rev cs1,rev vs1) of
	       (Bind((Lda,_),_,_,b1),c1::cs1,_::vs1) =>
		 unirec (dpth+1,maxd) false s (MkApp((subst1 c1 b1,cs1),vs1),f2)
	     | (_,cs1,vs1) => unirec (dpth+1,maxd) false s (MkApp((f1,cs1),vs1),f2))
	  | fold s ([],[],cs2,vs2) =
	    (case (f2,rev cs2,rev vs2) of
	       (Bind((Lda,_),_,_,b2),c2::cs2,_::vs2) =>
		 unirec (dpth+1,maxd) false s (f1,MkApp((subst1 c2 b2,cs2),vs2))
	     | (_,cs2,vs2) => unirec (dpth+1,maxd) false s (f1,MkApp((f2,cs2),vs2)))
	  | fold _ _ = bug"unirec; App; fold"
	val an = !UVARS
      in fold s (rev cs1,rev vs1,rev cs2,rev vs2)
	    handle unif => (handleUnif an;try_approx MN)
      end
********)
	| (App((f1,cs1),vs1),App((f2,cs2),vs2)) =>
	    let val an = !UVARS
	    in  let
		  val l1 = length cs1 and l2 = length cs2
		  val (f1,f2,cs1,cs2) =
		    if l1 = l2 then (f1,f2,cs1,cs2)
		    else if l1 < l2 
			   then let val l2l1 = l2-l1
				    val (pre,post) = chop_list l2l1 cs2
				    val (prev,postv) = chop_list l2l1 vs2
				in  (f1,App((f2,pre),prev),cs1,post)
				end
			 else let val l1l2 = l1-l2
				  val (pre,post) = chop_list l1l2 cs1
				  val (prev,postv) = chop_list l1l2 vs1
			      in  (App((f1,pre),prev),f2,post,cs2)
			      end
		in uniargs (unirec (dpth+1,maxd) false s (f1,f2)) (cs1,cs2)
		end                          (* in case of beta *)
	      handle unif => (handleUnif an;try_approx MN)
	    end
	| (Bind((Pi,vs1),_,M1,M2),Bind((Pi,vs2),_,N1,N2)) =>
	    if (!liberal_matching_switch orelse vs1=vs2)
	      then unirec (dpth+1,maxd) LMflg
                          (unirec (dpth+1,maxd) false s (M1,N1)) (M2,N2)
	    else raiseUnif("Pi",MN)
	| (Bind((Lda,vs1),_,M1,M2),Bind((Lda,vs2),_,N1,N2)) =>
	    unirec (dpth+1,maxd) false (unirec (dpth+1,maxd) false s (M1,N1)) (M2,N2)
	| (Bind((Sig,_),_,M1,M2),Bind((Sig,_),_,N1,N2)) =>
	    unirec (dpth+1,maxd) LMflg (unirec (dpth+1,maxd) LMflg s (M1,N1)) (M2,N2)
	| (Bind((Thry,_),_,_,_),Bind((Thry,_),_,_,_)) => bug"unif:Thry"
	| (Tuple(T1,ls1),Tuple(T2,ls2)) =>
	    if (length ls1)=(length ls2)
	      then uniargs (unirec (dpth+1,maxd) false s (T1,T2)) (ls1,ls2)
	    else raiseUnif("Tuples",MN)
	| (Proj(p1,c1),Proj(p2,c2)) =>
	    if p1<>p2 then try_approx MN
	    else (case (c1,c2) of
		    (Tuple _,Tuple _) =>   (* avoid traversing canonical tuples *)
		      (let
			 val (Mod M') = s1UMwhbenf ~1 M
			 val (Mod N') = s1UMwhbenf ~1 N
		       in unirec (dpth+1,maxd) LMflg s (M',N')
		       end handle Match => bug"unif:Proj Match")
		  | _ =>
		      let val an = !UVARS
		      in  (unirec (dpth+1,maxd) false s (c1,c2))
			(* in case projection *)
			handle unif => (handleUnif an; try_approx MN)
		      end)
(*********************************
  | (LabVT(_,M,_),LabVT(_,N,_)) => unirec (dpth+1,maxd) LMflg s (M,N)
  | (LabVT(_,M,_),N) => unirec (dpth+1,maxd) LMflg s (M,N)
  | (M,LabVT(_,N,_)) => unirec (dpth+1,maxd) LMflg s (M,N)
******************************)
	| (Theory,Theory) => s
	| _  => try_approx MN
end
in  
  let val an = !UVARS     (*** !! side efects !! ***)
      fun uniTop max_dpth =
	unirec (0,max_dpth) LMflg s (M,N)
	handle unif =>
	  (UVARS:= an;
	   if not (!unif_debug) then ()
	   else message("***unif caught at uniTop: "^makestring (!DpthExceeded));
	   if (!DpthExceeded) then
	     let val max_dpth = max_dpth*(!unif_deepen_factor)
		 val _ = DpthExceeded:= false
		 val _ = if not (!unif_debug) then ()
			 else message("***max_dpth increased to "^
				      (makestring max_dpth));
	     in  uniTop max_dpth
	     end
	   else raise Unif)
	     | unifVar =>
	       (UVARS:= an;
		if not (!unif_debug) then ()
		else message"***unifVar caught at UniTop";
		raise Unif)                           (* not quite right! *)
  in  uniTop (!unif_start_dpth)
  end
end;


fun type_match_unif s M N =         (* real unification *)
  let
    val _ = if !unif_debug
	     then (message"** type_match_unif_deb **";
		   print_expand M; print_expand N)
	   else ()
  in  SOME (Unirec true (!LuosMode) s (M,N))
      handle Unif => NONE
  end;
fun type_match_heur M N =         (* no variable instantiation *)
  let
    val _ = if !tm_debug
	     then (message"** type_match_heur_deb **";
		   print_expand M;print_expand N)
	   else ()
  in  (Unirec false (!LuosMode) [] (M,N);true)
      handle Unif => false
  end;

(************  partial unification first going to whnf  *************)

fun whnf_unif s M N =
  let
    exception whnfunif
    val _ = if not (!whun_debug) then ()
	    else (prs"**whun_deb** ";print_expand M;
		  prs"             ";print_expand N)
    fun unirec LMflg s (MN as (M,N)) =
      let
	fun reunion (p,P) M =
	  (* we guarantee that p is not bound in s, but M may be a meta-var.
	   * p and M may be the same meta-var, but that is not an occur check
	   *)
	  let
	    val ov = free_occur M
	    val mv = mv_occur p M
	  in
	    if mv orelse ov
	      then raise whnfunif
	    else let val tM = type_of_constr M
		     val s = unirec (!LuosMode) s (tM,P)
		 in compose sub [(p,M)] s
		 end
	  end

	fun uniargs s args1args2 = 
	  let fun uabod s mn = unirec false s mn 
	  in  foldl uabod s (ListUtil.zip args1args2 handle _ => bug"uniargs")
	  end

	fun clean c =
	  case c of
	    RedTyp(_) => bug"whun;clean RedTyp"
	  | Bot => bug"whun;clean Bot"
	  | CnLst(_) => bug"whun;clean CnLst"
	  | LabVT(_) => bug"whun;clean LabVT"
	  | _ =>  c
	val MN as (M,N) = (sub s (clean (UMwhnf M)),sub s (clean (UMwhnf N)))
	val _ = if not(!whun_debug) then ()
		else (prs"*whun_deb ";print_expand M;
		      prs"          ";print_expand N)
      in
	case MN
	  of (Var(mtm as (m,_)),Var(ntn as (n,_))) =>
	        if m=n then s
		else if m>n then reunion mtm N
		     else reunion ntn M
	   | (Var(mtm),_) => reunion mtm N
	   | (_,Var(ntn)) => reunion ntn M
	   | (Type(i),Type(j)) =>
	       if (if LMflg then univ_leq i j else univ_equal i j)
		 then s else raise whnfunif
	   | (Prop,Type(j)) => if LMflg then s else raise whnfunif
	   | (Prop,Prop) => s
	   | (Rel n,Rel m)  => if n=m then s else raise whnfunif
	   | (Ref b1,Ref b2) => if sameRef b1 b2 then s else raise whnfunif
	   | (App((f1,cs1),vs1),App((f2,cs2),vs2)) =>
	       if length cs1 <> length cs2 then raise whnfunif
	       else uniargs (unirec false s (f1,f2)) (cs1,cs2)
	   | (Bind((Pi,vs1),_,M1,M2),Bind((Pi,vs2),_,N1,N2)) =>
	       if (!liberal_matching_switch orelse vs1=vs2)
		 then unirec LMflg (unirec false s (M1,N1)) (M2,N2)
	       else raise whnfunif
	   | (Bind((Lda,vs1),_,M1,M2),Bind((Lda,vs2),_,N1,N2)) =>
	       unirec false (unirec false s (M1,N1)) (M2,N2)
	   | (Bind((Sig,_),_,M1,M2),Bind((Sig,_),_,N1,N2)) =>
	       unirec LMflg (unirec LMflg s (M1,N1)) (M2,N2)
	   | (Bind((Thry,_),_,_,_),Bind((Thry,_),_,_,_)) => bug"whun:Thry"
	   | (Tuple(T1,ls1),Tuple(T2,ls2)) =>
	       if (length ls1)=(length ls2)
		 then uniargs (unirec false s (T1,T2)) (ls1,ls2)
	       else raise whnfunif
	   | (Proj(p1,c1),Proj(p2,c2)) =>
	       if p1=p2 then unirec LMflg s (c1,c2) else raise whnfunif
	   | (Theory,Theory) => s
	   | _  => raise whnfunif
      end
  in  
    let val an = !UVARS     (*** !! side efects !! ***)
    in  SOME(unirec (!LuosMode) s (M,N))
      handle whnfunif => (UVARS:= an; NONE)
    end
  end;

end;
open Unif;
