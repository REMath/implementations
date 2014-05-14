(* eagerUnif.sml *)

(* A unifier that goes to whnf immediately, instead of checking
intentionally.  This will fail too often, so failure should be taken
lightly. *)

val eu_debug = ref false

eunif s c d : substitution option = 
  let
    exception euFail
    val an = !UVARS
    fun tm LMflg s (M,N) : =
      let
	val MN as (M,N) = (UMwhnf M,UMwhnf N)
	val _ = if !eu_debug
		  then (message"**eu_debug**";legoprint M;legoprint N)
		else ()
      in case MN of
	(Var(mtm as (m,_)),Var(ntn as (n,_))) =>
	  if m=n then s
	  else if m>n then reunion mtm N
	       else reunion ntn M
      | (Var(mtm),_) => reunion mtm N
      | (_,Var(ntn)) => reunion ntn M
      | (Type i,Type j) => if LMflg then univ_leq i j else univ_equal i j
	    | (Prop,Type j) => LMflg
	    | (Prop,Prop) => s 
	    | (Rel n,Rel m) => n=m
	    | (Ref(b1),Ref(b2)) => sameRef b1 b2
	    | (App((f1,cs1),_),App((f2,cs2),_)) =>
		(tm LMflg (f1,f2)) andalso
		(for_all (tm LMflg)
		 (ListUtil.zip (cs1,cs2)) handle Zip => false)
	    | (Bind((Pi,vs1),_,M1,M2),Bind((Pi,vs2),_,N1,N2)) =>
		(!liberal_matching_switch orelse vs1=vs2) andalso
		(tm false (M1,N1)) andalso tm LMflg (M2,N2)
	    | (Bind((Sig,_),_,M1,M2),Bind((Sig,_),_,N1,N2)) =>
		(tm LMflg (M1,N1)) andalso tm LMflg (M2,N2)
	    | (Proj(p1,c1),Proj(p2,c2)) =>
		(p1=p2) andalso (tm false (c1,c2)) (**?????????????**)
	    | (Bind((Lda,vs1),_,M1,M2),Bind((Lda,vs2),_,N1,N2)) =>
		(tm false (M1,N1)) andalso tm LMflg (M2,N2)
	    | (Tuple(T1,ls1),Tuple(T2,ls2)) => 
		tm false (T1,T2) andalso
		(for_all (tm false)
		 (ListUtil.zip(ls1,ls2)) handle Zip => false)
	    | (CnLst ls1,CnLst ls2) => 
		(for_all (tm false) (ListUtil.zip(ls1,ls2)) handle Zip => false)
	    | (Var(n,_),Var(m,_)) => n=m
	    | (_,_) => false
      end
  in
    tm (!LuosMode) (c,d) orelse (UVARS:= an; false)
  end;
