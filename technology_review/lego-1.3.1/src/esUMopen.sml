(* UMopen.sml *)
(* Lescanne's weak/strong normalization on open terms *)

(* 21/Oct/98 Conor changes pattern compiler to expand local definitions *)

val um_debug = ref false;
val ae_debug = ref false;
val tm_debug = ref false;
val sp_debug = ref false;
val pat_debug = ref false;
val share_debug = ref false;
val dnf_debug = ref false;
val st_debug = ref false;      (* sameTerm *)

val liberal_matching_switch = ref true;
val pat_norm_switch = ref false;

val toc = ref (fn (x:cnstr) => x)  (* foward reference to toc *)

structure UMopen :
  sig 
    val UMnorm : cnstr -> cnstr
    val UMwhnf : cnstr -> cnstr
    val thryUMwhnf : cnstr -> cnstr
    val UMdnf : cnstr -> cnstr
    val UMpnf : cnstr -> cnstr
    val UMtype_match : cnstr -> cnstr -> bool
    val sameTerm : cnstr -> cnstr -> bool
    val rUMwhnf : cnstr -> cnstr modif
    val s1UMwhbenf : int -> cnstr -> cnstr modif
    datatype dfnFlgs = DF of {beta:bool,gdfn:bool,ldfn:bool,spdfn:bool}
    val whnfP : dfnFlgs -> cnstr -> bool
    val init_reductions : unit -> unit
    val add_reductions : cnstr -> unit
  end =
struct


  fun sameTerm c d =
    let
      val an = !UVARS
      fun flre opn = if not (!st_debug) then () else opn()
      val _ = flre (fn()=> (prs"**sT_deb t l: "; print_expand c;
			    prs"         t r: "; print_expand d))
      fun samTrm cd =
	case cd of
	  (Bind((bt1,_),_,l1,r1),Bind((bt2,_),_,l2,r2)) =>
	    (if bt1=bt2 then true
	     else (flre (fn()=> message"**sT_deb f: bind type"); false))
	    andalso samTrm (l1,l2) andalso samTrm (r1,r2)
	| (Ref br1,Ref br2) =>
	    if sameRef br1 br2 then true
	    else (flre (fn()=> message("**sT_deb f: Ref "^
				       (ref_nam br1)^" "^(ref_nam br2)));
		  false)
	| (Rel n1,Rel n2) =>
	    if n1=n2 then true
	    else (flre (fn()=> message("**sT_deb f: Rel "^
				       (makestring n1)^" "^(makestring n2)));
		  false)
	| (Tuple(t1,cs1),Tuple(t2,cs2)) =>
	    (samTrm(t1,t2) andalso for_all samTrm (ListUtil.zip (cs1,cs2))
	     handle ListUtil.Zip =>
	       (flre (fn()=> message"**sT_deb f: Tuple"); false))
	| (Type n1,Type n2) =>
	    if (if (!LuosMode) then univ_leq n1 n2 else univ_equal n1 n2)
	      then true
	    else (flre (fn()=> message"**sT_deb f: TypeType"); false)
	| (Prop,Type _) =>
	    if (!LuosMode) then true
	    else (flre (fn()=> message"**sT_deb f: PropType"); false)
	| (Prop,Prop) => true
	| (Theory,Theory) => true
	| (App((f1,as1),_),App((f2,as2),_)) =>
	    (samTrm(f1,f2) andalso for_all samTrm (ListUtil.zip (as1,as2))
	     handle ListUtil.Zip =>
	       (flre (fn()=> message"**sT_deb f: App"); false))
	| (Proj(p1,t1),Proj(p2,t2)) =>
	    (if p1=p2 then true
	     else (flre (fn()=> message"**sT_deb f: proj"); false))
	    andalso samTrm(t1,t2)
	| (RedTyp(_,c1),RedTyp(_,c2)) => samTrm(c1,c2)
	| (Var(n,_),Var(m,_)) =>
	    if n=m then true
	    else (flre (fn()=> message("**sT_deb f: Var "^
				       (makestring n)^" "^(makestring m)));
		  false)
	| (LabVT(l1,c1,t1),LabVT(l2,c2,t2)) =>
	    (if l1=l2 then true
	     else (flre (fn()=> message"**sT_deb f: LabVT"); false))
	    andalso samTrm(c1,c2) andalso samTrm(t1,t2)
	| (CnLst cs1,CnLst cs2) =>
	    (for_all samTrm (ListUtil.zip (cs1,cs2))
	     handle ListUtil.Zip =>
	       (flre (fn()=> message"**sT_deb f: CnLst"); false))
	| (Bot,Bot) => bug"UM,samTrm;Bot"
	| (x,y) =>
	     (flre (fn()=> (prs"**sT_deb f l: "; print_expand x;
			    prs"         f r: "; print_expand y));
	      false)
    in samTrm (c,d) orelse (UVARS:= an; false)
    end;


  (** patterns for the rewrite operations **)
datatype pat =
    Pcons of binding                               (* globals *)
  | Pmv of int                                     (* match vars *)
  | Papp of pat * (pat list)
  | Pprop
  | Ptype of node
(* print patterns for debugging *)
local
  val rec pp =
    fn Pcons(Bd{bd=(bv,s,c,d),...}) => prs s
     | Pmv(s) => prs("["^makestring s^"]")
     | Papp(p,args) =>
	 (prs"("; pp p; prs" ";
	  do_list (fn x => (pp x;prs" ")) args; prs")")
     | Pprop => prs"Prop"
     | Ptype(n) => prs"Type"
in
  fun print_pat pat = (pp pat; line())
end;

fun pat_head_const_args lhs p =
  case p
    of (Pcons br) => (br,0)
     | Papp(p',args) => (#1(pat_head_const_args lhs p'),length args)
     | _ => (prs"LHS of rewrite has no head constant: ";
	     legoprint lhs;
	     failwith"reductions not accepted")

type reduction = int*int*pat*cnstr (* nbr args, nbr match vars, LHS, RHS *)
type reductions = reduction list;

(** for hashing reductions on the binding, br, of the head Ref(br) of LHS **)
structure HashReds :
  sig
    val init_reductions : unit -> unit
    val add_reductions : reductions -> unit
    val find_reductions : binding -> reductions
  end =
  struct
    (* first int is timestamp of the head constant *)
    type my_reds = int * reductions 
    val TableSize = 701
    val HashTable = (* entries are (my_reds list) in case of hashing conflict *)
      ref (Array.array(TableSize,nil) : (my_reds list) Array.array)

    fun init_reductions() = HashTable:= Array.array(TableSize,nil)

    fun hash (ts:int) = ts mod TableSize

    fun add_reduction (red as (_,_,lhs,_)) =
      let
	val (hbr,_) = pat_head_const_args Bot lhs
	val phc = ref_ts hbr
	val i = hash phc
	val old_i = Array.sub(!HashTable,i)
	fun same_key ((n,_):my_reds) =  phc = n
	val (this_one,others) = split same_key old_i
	val _ = if not (!pat_debug) then ()
		else (prs"**add_red; "; print_pat lhs)
	val new_this_one = case this_one
			     of [] => (phc,[red])
			      | [(_,reds)] => (phc,reds@[red])
			      | x => bug("add_reduction: "^makestring(length x))
      in  Array.update(!HashTable,i,new_this_one::others)
      end
    val add_reductions = do_list add_reduction

    fun find_reductions (br:binding) =
      let
	val tsbr = ref_ts br
	val all_iReds = Array.sub(!HashTable,hash tsbr)
      in
	assoc tsbr all_iReds handle Assoc => []
      end

  end;  (*  struct HashReds  *)
open HashReds;


datatype closure = Clos of (cnstr * env)
and envClos = EC of closure | Shift
and stackClos =
  SC of (closure * stack) ref * prntVisSort
| SFST
| SSND
| SLBL of string * closure
withtype env = (envClos * int) list
and stack = stackClos list;

fun Share cl ces =
  let
    val _ = if not (!share_debug) then ()
	    else let
		   val (Clos(ot,_),_) = !cl
		   val (Clos(nt,_),_) = ces
		 in (prs"**share_deb: old ";legoprint ot;
		     prs"**share_deb: new ";legoprint nt)
		 end
  in
    cl:= ces
  end


type state = bool * env * stack * cnstr;
datatype dfnFlgs = DF of {beta:bool,gdfn:bool,ldfn:bool,spdfn:bool}
fun gdfn (DF{gdfn=b,...}) = b
fun beta (DF{beta=b,...}) = b
fun ldfn (DF{ldfn=b,...}) = b
fun spdfn (DF{spdfn=b,...}) = b
val trueDF = DF{beta=true,gdfn=true,ldfn=true,spdfn=true}

(* substitution can't change this sound but incomplete test *)
fun whnfP (dfnf:dfnFlgs) c =
  let
    fun whnfrec x =
    case x of
      Bind((bt,_),_,_,_) => bt<>Let orelse not (ldfn dfnf)
    | Ref br => not (gdfn dfnf andalso ref_isDefnNow br) andalso
	(not (spdfn dfnf) orelse find_reductions br=[])
    | Rel _ => true
    | Tuple _ => true
    | Type _ => true
    | Prop => true
    | Theory => true
    | App((f,_),_) => whnfrec f andalso not (isLda f)
    | Proj(_,t) => whnfrec t andalso not (isTuple t orelse isThry t)
    | RedTyp(_,t) => whnfrec t
    | Var _ => false
    | LabVT _ => bug"UM,whnfP;LabVT"
    | CnLst _ => bug"UM,whnfP;CnLst"
    | Case _ => bug"UM,whnfP;Case"
    | Bot => bug"UM,whnfP;Bot"
  in whnfrec c
  end
 

(**  for debugging  **)
fun prtenv (e:env) =
  let val msnat = makestring
      val aux =
	fn (EC(Clos cl),n) =>
	     (case cl of
		(t,[]) => (prs" !"; prnt t; prs(","^(msnat n)^" "))
	      | (t,_) => (prs" *"; prnt t; prs(","^(msnat n)^" ")))
	 | (Shift,n) => prs(" ^"^(msnat n)^" ")
  in  prs"env "; do_list aux e; line()
  end
fun prtstack (s:stackClos list) =
  let val aux =
    fn SC(Cl,_) =>
        (case !Cl of
	   (Clos(t,[]),[]) => (prs" !"; prnt t; prs" ")
	 | (Clos(t,_),_) => (prs" *"; prnt t; prs" "))
     | SFST => prs" Fst "
     | SSND => prs" Snd "
     | SLBL(s,_) => prs("."^s)
  in  prs"stk "; do_list aux s; line()
  end
fun prtDfnFlgs (DF{beta,gdfn,ldfn,spdfn}) =
  "("^makestring beta^","^makestring gdfn^","^
  makestring ldfn^","^makestring spdfn^")";


(**********************************************
fun evalState (Clos cl) =
  let
    fun unwArgs (t,stk) =
      let
	(* here we optimize appending in MkApp using (cs,vs) as accumulator *)
	val nilnil = ([],[])
	fun lMkApp (trm,(cs,vs)) = MkApp((trm,cs),vs)
	fun aux sc (atrm as (trm,(cs,vs))) =
	  case sc of
	    SC(cl,v) => (trm,(evalState cl::cs,v::vs))
	  | SFST => (MkProj(Fst,lMkApp atrm),nilnil)
	  | SSND => (MkProj(Snd,lMkApp atrm),nilnil)
	  | SLBL(s,_) => (MkProj(Labl(s),lMkApp atrm),nilnil)    (* use trm or cl ? *)
      in  lMkApp (foldr aux (t,nilnil) stk)
      end
  in
    case !cl of
      (t,[],p) => unwArgs (t,p)
    | (t,e,p) =>
	let fun sbstClos e =
	  fn Rel n => evalState(acc_env(n,e))
	   | App(bod) => umkApp (sbstClos e) bod
	   | Bind(x,y,l,r) => MkBind(x,y,sbstClos e l,sbstClos (lft_env e) r)
	   | Tuple(bod) => umkTuple (sbstClos e) bod
	   | CnLst(bod) => umkCnLst (sbstClos e) bod
	   | Proj(bod) => umkProj (sbstClos e) bod
	   | RedTyp(bod) => umkRedTyp (sbstClos e) bod
	   | Var(bod) => umkVar (sbstClos e) bod
	   | LabVT(bod) => umkLabVT (sbstClos e) bod
	   | t => t
	in unwArgs(sbstClos e t,p)
	end
  end
*******************************************)

fun evalState (Clos(t,e),p) =
  let
    fun unwArgs (t,stk) =
      let
	fun aux trm =
	  fn SC(cl,v) => MkApp((trm,[evalState (!cl)]),[v])
	   | SFST => (MkProj(Fst,trm))
	   | SSND => (MkProj(Snd,trm))
	   | SLBL(s,_) => (MkProj(Labl(s),trm))    (* use trm or cl ? *)
      in  foldl aux t stk
      end
  in
    case e of
      [] => unwArgs (t,p)
    | _ => let fun sbstClos e =
	fn Rel n => evalState(acc_env(n,e),[])
	 | App(bod) => umkApp (sbstClos e) bod
	 | Bind(x,y,l,r) => MkBind(x,y,sbstClos e l,sbstClos (lft_env e) r)
	 | Tuple(bod) => umkTuple (sbstClos e) bod
	 | CnLst(bod) => umkCnLst (sbstClos e) bod
	 | Proj(bod) => umkProj (sbstClos e) bod
	 | RedTyp(bod) => umkRedTyp (sbstClos e) bod
	 | Var(bod) => umkVar (sbstClos e) bod
	 | LabVT(bod) => umkLabVT (sbstClos e) bod
	 | t => t
	   in unwArgs(sbstClos e t,p)
	   end
  end

(* optimise lifting the environment and appending the new item
 * on the back
 *)
and gen_lft_env (n:int) cs =
  let fun le [] = cs
	| le ((c,i)::e) = (c,n+i)::le e
  in le
  end
and lft_app e d = gen_lft_env 1 [(d,0)] e
and lft_env e = gen_lft_env 1 [] e
(* multiple beta-steps at once to avoid repeated lift_env *)
and lda_bet_star (env,stk,t) =
  let
    fun count (SC(Cl,_)::stk,Bind((Lda,_),_,_,c),args) = count (stk,c,(!Cl)::args)
      | count x = x
    val (nstk,nc,args) = count (stk,t,[])
    fun env_args (Sn as (n,eargs)) =
      fn [] => Sn
       | (c,[])::args => env_args (n+1,(EC c,n)::eargs) args
       | cp::args => env_args (n+1,(EC(Clos(evalState cp,[])),n)::eargs) args
    val (n,eargs) = env_args (0,[]) args
  in
    (true,gen_lft_env n eargs env,nstk,nc)
  end

and unload ((prog,env,stk,t):state) : cnstr modif =
  let
    val ans = if prog then Mod(evalState(Clos(t,env),stk))
	      else UMod
    val _ = if not(!um_debug) then ()
	    else (prs"**unload_debug; output ";
		  case ans
		    of UMod => message"no progress"
		     | Mod(t) => print_expand t)
  in  ans
  end
and acc_env (n,env) : closure =
  let
    val ShZe = (Shift,0);
    val _ = if not(!ae_debug) then ()
	    else (prs("**ae_debug; "^(makestring n)^": "); prtenv env)
    fun Rel1 env : closure =      (* n=1  *)
      let 
	val _ = if not(!ae_debug) then ()
		  else (prs("**ae_debug1: "); prtenv env)
      in case env
	   of [] => Clos(Rel 1,[])
	    | (c,m)::e =>
		(if m>0 then (Rel1 e : closure)
		 else case c of
		   Shift => (acc_env(2,e) : closure)
		 | EC(Cl as (Clos(a,f))) => (* if e=[] then Cl else Clos(a,f@e) *)
		     case (e,a)
		       of ([],_) => Cl
			| (_,Rel i) => acc_env (i,f@e)
			| _ => Clos(a,f@e))
      end
    (* n>1, env non-empty, only grows *)
    fun nSuc c : int * int * (envClos * int) list -> closure = 
      let
	fun aux (n,i,e) : closure =
	  case i
	    of 0 => (acc_env(if c=Shift then n+1 else n-1,e) : closure)
	     | m => let val j = m-1
		    in if n>2 then (aux(n-1,j,ShZe::e) : closure)
		       else (Rel1((c,j)::ShZe::e) : closure)
		    end
      in aux
      end
  in
    (case env of
       [] => (Clos(Rel n,[]) : closure)
     | (Shift,0)::e => (acc_env(n+1,e) : closure)
     | (c,i)::e => if n=1 then (Rel1 env : closure) else (nSuc c (n,i,e) : closure)
	 : closure)
  end
(* we have seperate flags to set whether to make progress or not on
 * global defns, local defns, and special defns.  We also take a set
 * of flags to update the working flags the first time progress is made,
 * so as to support expanding one defn, then only beta-redexes
 *)
(* thrydfn tells whether or not to expand a defn whose value is a theory
 * when it is not the subject of a projection
 *)
(* forceWindup tells whether or not to build the environment even if the
 * term is a whnf.  We force if we intend to go under a binder as in
 * computing a normal form or dnf
 *)
(* stopTS says to stop reducing if some progress has been made, and the
 * head constant has this timestamp. *)
and UM (stopTS:int)
       (forceWindup:bool,thrydfn:bool) (dfn:dfnFlgs,stpDfn:dfnFlgs)
       ((PROG,ENV,STK,TRM):state) : state =
  let
    val curDfn = ref dfn
    val _ = if not(!um_debug) then ()
	    else (message("**UM_debug; "^(makestring thrydfn)^", "^
			 (makestring (whnfP dfn TRM))^", "^
			 prtDfnFlgs dfn^", "^prtDfnFlgs stpDfn);
		  print_expand TRM)
    (** ref for toplevel progree ?? **)
    fun um (state as (prog:bool, env:env, stk:stack, t:cnstr):state) : state =
      let
	val _ = if not(!um_debug) then ()
		else (prs("**um_debug; input "^(makestring prog)^", ");
		      print_expand t; prtenv env; prtstack stk)
	(* if progress was made, swap dfn flags *)
	fun showProgress() = (curDfn:= stpDfn; true)
	fun stop st = st
	fun special br =
	  let
	    exception nomatch
	    fun raise_nomatch s =
	      (if not (!sp_debug) then ()
	       else message("**sp_deb; nomatch: "^s);
	       raise nomatch)
	    fun args_from_stk x =
	      case x
		of ([],stk) => ([],stk)
		 | (pa::pas,(sc as (SC _))::stk) =>
		     (case args_from_stk(pas,stk)
			of (zips,stk) => ((sc,pa)::zips,stk))
		 | _ => raise_nomatch("stack too short")
	    val spProg = ref prog  (** ref for toplevel progree ?? **)
	    val reds = find_reductions br
	    val _ = if not (!sp_debug) then ()
		    else (message("**sp_deb; head= "^ref_nam br^
				  ", nbr reds= "^makestring (length reds));
			  if reds=[] then ()
			  else (prtenv env; prtstack stk))
	    fun UMclos brp = UM brp (true,false) (trueDF,trueDF)
	    fun buildMatch menv =
	      fn (SC(Cl,_),Pmv s) =>  (* repeated vars ok in match if convertible *)
	         let val cl = !Cl
		 in  ((if UMtm cl (assoc s menv) then menv
		       else raise_nomatch("non-linear arg fails: "^makestring s))
		      handle Assoc => (s,cl)::menv)
		 end
	       | (SC(Cl,_),p) =>
		   (* when p not Pmv, c is computed for the right constructor *)
		   let
		     val ts = case p
				of Pcons brp => ref_ts brp
				 | Papp(Pcons brp,_) => ref_ts brp
				 | _ => ~1
		     val (Clos(c,e),s) = !Cl
		     val (prog,env,stk,c) = UMclos ts (prog,e,s,c)
		     val _ = spProg := (!spProg orelse prog)
		     val _ = Share Cl (Clos(c,env),stk)
		   in
		     case (stk,c,p) of
		       (_,Ref brc,Pcons brp) =>
			 if sameRef brc brp then menv
			 else raise_nomatch("different constructors: "^
					    ref_nam brc^", "^ref_nam brp)
		     | (stk,Ref brc,Papp(Pcons brp,pas)) =>  (***)
			 if sameRef brc brp
			   then
			     let
			       val (pairs,nstk) = args_from_stk (pas,stk)
			       val _ = if nstk=[] then ()
				       else bug"buildmatch;too many args"
			     in  foldl buildMatch menv pairs
			     end
			 else raise_nomatch("different constructors: "^
					    ref_nam brc^", "^ref_nam brp)
		     | (_,Prop,Pprop) => menv
		     | (_,Type n,Ptype m) =>
			 if node_equal n m then menv else raise nomatch
		     | _ => raise_nomatch"different shape"
		   end
	       | _ => bug"buildMatch: other"
	    fun menv2stk (menv,m) =
	      let
		fun me2s M stk =
		  if m<M then stk
		  else 
		    let val cl = assoc M menv
		      handle Assoc => (Clos(Bot,[]),[])
		    in  me2s (M+1) (SC(ref cl,NoShow)::stk)
		    end
	      in  me2s 1
	      end
	    fun specrec [] = stop(!spProg,env,stk,t)
	      | specrec ((n,m,p,c)::rest) =
		(let
		   val _ = if not (!sp_debug) then ()
			   else (message("**sp_deb; try reduction, args= "^
					 makestring n^", #matchvars= "
					 ^makestring m);
				 prs"LHS: "; print_pat p;
				 prs"RHS: "; legoprint c)
		   val (nstk,nc) =
		     case p of
		       Pcons _ => (menv2stk ([],m) [],c)
		     | Papp(_,pas) =>
			 let
			   val (pairs,nstk) = args_from_stk (pas,stk)
			   val menv = foldl buildMatch [] pairs
			 in (menv2stk (menv,m) nstk,c)
			 end
		     | _ => bug"specrec:illegal pattern"
		   val _ = if not (!sp_debug) then ()
			   else message("**sp_deb; special succeeds for "
					^ref_nam br)
		 in um(showProgress(),[],nstk,nc)     (* env MUST be nil *)
		 end handle nomatch => specrec rest)
    	  in specrec reds
	  end

	fun caseApp ((c,cs),vs) =
	  let
	    fun pa c =
	      case c of
		Ref br => Clos(c,[])
	      | Rel n => acc_env(n,env)
	      | Prop => Clos(c,[])
	      | Type _ => Clos(c,[])
	      | Theory => Clos(c,[])
	      | _ => Clos(c,env)
	    fun aux ((c,v):cnstr*prntVisSort) (s:stack) : stack =
	      SC(ref(pa c,[]),v)::s
	  in
	    um (prog,env,foldr aux stk (ListUtil.zip(cs,vs)),c)
	  end
	fun caseBind (bv as (bt,_),nam,l,r) =
	  case (stk,bt) of
	    (_,Let) =>                      (* local definition *)
	      if ldfn(!curDfn)
		then um(showProgress(),lft_app env (EC(Clos(l,env))),stk,r)
	      else stop(state)
	  | ([],_) => stop(state)            (* in whnf *)
	  | (_::_,Lda) =>                    (* beta redexes *)
	      if beta (!curDfn)
		then (showProgress(); um(lda_bet_star(env,stk,t)))
	      else stop(state)
	  (* project from theory: only if global defn's expanded *)
	  | (SLBL(s,cl)::stk',Thry) =>
	      let
		fun assoc (LabVT(Name l,a,_)::rest) =
		       if s=l then a else assoc rest
		  | assoc _ = bug"um:Bind:assoc"
		val lvts = case r
			     of CnLst lvts => lvts
			      | _ => bug"um:Bind,Thry"
	      in 
		um(showProgress(),lft_app env (EC cl),stk',assoc lvts)
	      end
	   (*****************************
	  (* project from parameterised theory *)
	  | (SLBL(s,cl)::stk',Lda) =>
	    um(showProgress(),env,stk',Bind(bv,nam,l,Proj(Labl s,r)))
	  *****************************)
	  | _ => bug"um: Bind"
	fun caseRef br =      (** all definitions are closed: forget env **)
	  if prog andalso stopTS=ref_ts br then stop(state)
	  else if ref_isDefnNow br andalso gdfn(!curDfn)
		 then um (showProgress(),[],stk,ref_VAL br)
	       else if ref_isDefn br orelse not (spdfn(!curDfn))
		      then stop(state)
		    else special br    (* try rewrite *)
	fun caseRel n =
	  case acc_env(n,env) of
	      Clos(relm as (Rel _),[]) => stop(prog,[],stk,relm)
	    | Clos(a,e) => um(showProgress(),e,stk,a)
	fun caseProj (p,c) =
	  case p of
	    Fst => um(prog,env,SFST::stk,c)
	  | Snd => um(prog,env,SSND::stk,c)
	  (* theory projection is like defn expansion *)
	  | Labl(s) => if gdfn(!curDfn)
			 then um(prog,env,SLBL(s,Clos(c,env))::stk,c)
		       else stop(state)
	fun caseTuple (T,cs) =
	  case (stk,cs)
	    of (SFST::nstk,l::_) => um(showProgress(),env,nstk,l)
	     | (SSND::nstk,_::[r]) => um(showProgress(),env,nstk,r)
	     | (SSND::nstk,l::ls) =>
		 (case gUMwhnf env T
		    of Bind(_,nm,_,S) => 
		      um(showProgress(),env,nstk,MkTuple(subst1 l S,ls))
		     | _ => bug"um: type of tuple")
	     | _ => stop(state)
	fun caseCase _ = bug"UM case"
(*************************
	  let
	    fun stripLocs pr =
	      case pr of
		Bind((Lda,vis),n,lbl,bod) =>
		  let val (mvars,Lhs,Rhs) = stripLocs bod
		  in  (mvars+1,Lhs,Bind((Lda,vis),n,lbl,Rhs))
		  end
	      | LabVT(RedPr,lhs,rhs) => (0,lhs,rhs)
	      | _ => (prs"not a pattern: ";legoprint c;
		      failwith"not a pattern")
            fun findBranch br nvars = 
	      let
		fun fb [] => NONE
		  | fb (brnch::brnchs) =
		    case stripLocs brnch of
		      (_,Ref br',rhs) =>
			if sameRef br br' andalso nvars=0
			  then SOME(***)
			else fb brnchs
		    | (mvars,App((Ref br',cs),_),rhs) => 
			if sameRef br br' andalso nvars=mvars
			  then SOME(***)
			else fb brnchs
		    | _ => bug"UM;fb"
	      in fb branches
	      end

	  case um(false,env,[],c) of
	    (caseProg,caseEnv,caseStk,Ref br) => 
	      

	      
*********************)
      in
(*******************
	if not thrydfn andalso env=[] andalso
	   (!toc) t = Theory andalso
	   case stk of (SLBL _)::_ => false | _ => true
	  then stop(state)
	else
*************************)
	case t of
	  App bod => caseApp bod
	| Bind bod => caseBind bod
	| Ref bod => caseRef bod
	| Rel n => caseRel n
	| Proj bod => caseProj bod
	| Tuple bod => caseTuple bod
	| Case bod => caseCase bod
	| LabVT(_,v,_) => um(showProgress(),env,stk,v)  (* progress?? *)
	| _ => stop(state)
  end
  in if not forceWindup andalso ENV=[] andalso STK=[] andalso whnfP dfn TRM
	then (PROG,ENV,STK,TRM)
      else (um(PROG,ENV,STK,TRM):state)
  end
and sgwhnf stopTS thrydfn (dfn:dfnFlgs) (stpDfn:dfnFlgs)
                   (env:env) (t:cnstr) : cnstr modif =
  unload (UM stopTS (false,thrydfn) (dfn,stpDfn) (false,env,[],t))
and gwhnf thrydfn (dfn:dfnFlgs) (env:env) (t:cnstr) : cnstr =
  case sgwhnf ~1 thrydfn dfn dfn env t
    of UMod => t
     | Mod(c) => c
and gUMwhnf env c = gwhnf false trueDF env c
and rUMwhnf c = sgwhnf ~1 false trueDF trueDF [] c
(* one step then to whbenf *)
and s1UMwhbenf stopTS c = sgwhnf stopTS false trueDF 
                          (DF{beta=true,gdfn=false,ldfn=true,spdfn=false}) [] c
and UMwhnf c = gwhnf false trueDF [] c
(* special for typechecking theory projections *)
and thryUMwhnf c = gwhnf true trueDF [] c
and gnorm (dfn:dfnFlgs) : cnstr -> cnstr =
(**********************
  let
    fun gnEnv env =
      fn Bind(bt,y,l,r) => MkBind(bt,y,gnEnv env l,gnEnv (lft_env env) r)
       | Tuple bod => umkTuple (gnEnv env) bod
       | CnLst bod => umkCnLst (gnEnv env) bod
       | LabVT bod => umkLabVT (gnEnv env) bod
       | Proj bod => umkProj (gnEnv env) bod
       | RedTyp bod => umkRedTyp (gnEnv env) bod
       | Var bod => umkVar (gnEnv env) bod
       | hd => hd

    fun normCl env =
      fn Bind(bt,y,l,r) => MkBind(bt,y,normCl env l,normCl (lft_env env) r)
       | Tuple bod => umkTuple (normCl env) bod
       | CnLst bod => umkCnLst (normCl env) bod
       | LabVT bod => umkLabVT (normCl env) bod
       | Proj bod => umkProj (normCl env) bod
       | RedTyp bod => umkRedTyp (normCl env) bod
       | Var bod => umkVar (normCl env) bod
       | hd => hd
    fun gndfn (Cl as (Clos cl)) =
      let
	fun opn cl =
	  let
	    val (t,e,p) = !cl
	    val (_,env,stk,hd) =  UM ~1 (true,false) (dfn,dfn) (false,e,p,t)

	    fun normHd env =
	      fn Bind(bt,y,l,r) => MkBind(bt,y,normHd env l,normHd (lft_env env) r)
	       | Tuple bod => umkTuple (normHd env) bod
	       | CnLst bod => umkCnLst (normHd env) bod
	       | LabVT bod => umkLabVT (normHd env) bod
	       | Proj bod => umkProj (normHd env) bod
	       | RedTyp bod => umkRedTyp (normHd env) bod
	       | Var bod => umkVar (normHd env) bod
	       | hd => hd
	    fun evcl (Cl as (Clos cl)) =
	      case !cl of (c,e,p) =>
		let
		  val nf = normHd e c
		(*  val _ = Share Cl (nf,[],[])  *)
		in  nf
		end
	  in  opnClos opn CL
	  end
      in  opnClos opn CL
  end
************************)
  let
    fun gndfn (p:stack) (env:env) (t:cnstr) : cnstr =
      let
	val _ = if not(!dnf_debug) then ()
		else (prs"**dnf_deb: ";print_expand t;
		       prtenv env; prtstack p)
	val (_,env,stk,hd) =  UM ~1 (true,false) (dfn,dfn) (false,env,p,t)
	val hd =
	  case hd of
	    Bind(bt,y,l,r) =>
	      MkBind(bt,y,gndfn [] env l,gndfn [] (lft_env env) r)
	  | Tuple bod => umkTuple (gndfn [] env) bod
	  | CnLst bod => umkCnLst (gndfn [] env) bod
	  | LabVT bod => umkLabVT (gndfn [] env) bod
	  | Proj bod => umkProj (gndfn [] env) bod
	  | RedTyp bod => umkRedTyp (gndfn [] env) bod
	  | Var bod => umkVar (gndfn [] env) bod
	  | _ => hd
	fun evcl Cl = case !Cl of (Clos(c,e),p) => gndfn p e c
	fun aux trm =
	  fn SC(cl,v) => MkApp((trm,[evcl cl]),[v])
	   | SFST => (MkProj(Fst,trm))
	   | SSND => (MkProj(Snd,trm))
	   | SLBL(s,cl) => (MkProj(Labl(s),trm))
	val ans = foldl aux hd stk
	val _ = if not(!dnf_debug) then ()
		else (prs"**dnf_deb: output ";print_expand ans)
      in  ans
      end
  in gndfn [] []
  end

and UMnorm c = gnorm trueDF c
                                         (** spdfn false ?? **)
and UMdnf c = gnorm (DF{beta=true,gdfn=false,ldfn=false,spdfn=true}) c
and UMpnf c = gnorm (DF{beta=false,gdfn=false,ldfn=false,spdfn=false}) c

and UMtm (Clos(c1,e1),p1) (Clos(c2,e2),p2) =
  let
    val an = !UVARS
    fun tm LMflg (pM,pN) (envM,envN) (M,N) =
      let
	val nilnil = ([],[])
	val UMclos = UM ~1 (true,false) (trueDF,trueDF)
	val ((_,envM,stkM,M),(_,envN,stkN,N)) =
	  (UMclos (false,envM,pM,M),UMclos (false,envN,pN,N))
	val _ = if not (!tm_debug) then ()
	        else (message"** UMtm_debug **";legoprint M;legoprint N)
	val tmStk =
	  fn (SC(Cl1,_),SC(Cl2,_)) =>
	  (case (!Cl1,!Cl2) of ((Clos(c1,e1),p1),(Clos(c2,e2),p2)) =>
	     tm LMflg (p1,p2) (e1,e2) (c1,c2))
	   | (SFST,SFST) => true
	   | (SSND,SSND) => true
	   | (SLBL(s1,_),SLBL(s2,_)) => s1=s2
	   | _ => false
      in
	(case (M,N) of
	   (Type i,Type j) => if LMflg then univ_leq i j
			      else univ_equal i j
	 | (Prop,Type j) => LMflg
	 | (Prop,Prop) => true
	 | (Rel n,Rel m) => n=m
	 | (Ref(b1),Ref(b2)) => sameRef b1 b2
	 | (Bind((bt1,vs1),_,M1,M2),Bind((bt2,vs2),_,N1,N2)) =>
	     bt1=bt2 andalso
	     (case bt1 of
		Pi =>
		  (!liberal_matching_switch orelse vs1=vs2) andalso
		  tm false nilnil (envM,envN) (M1,N1) andalso
		  tm LMflg nilnil (lft_env envM,lft_env envN) (M2,N2)
	      | Sig =>
		  tm LMflg nilnil (envM,envN) (M1,N1) andalso
		  tm LMflg nilnil (lft_env envM,lft_env envN) (M2,N2)
	      | Lda =>   (**  ??? bug  ??? **)
		  tm false nilnil (envM,envN) (M1,N1) andalso
		  tm LMflg nilnil (lft_env envM,lft_env envN) (M2,N2)
	      | Thry => bug"UMtype_match: Thry"
	      | Let => bug"UMtype_match: Let")
	 | (Tuple(T1,ls1),Tuple(T2,ls2)) => 
	     (tm false nilnil (envM,envN) (T1,T2) andalso
	      for_all (tm false nilnil (envM,envN))
	      (ListUtil.zip(ls1,ls2)) handle Zip => false)
	 | (CnLst ls1,CnLst ls2) => 
	     (for_all (tm false nilnil (envM,envN))
	      (ListUtil.zip(ls1,ls2)) handle Zip => false)
	 | (LabVT(s1,v1,t1),LabVT(s2,v2,t2)) =>
	     s1=s2 andalso
	     tm false nilnil (envM,envN) (v1,v2) andalso
	     tm false nilnil (envM,envN) (t1,t2)
	 | (Var(n,_),Var(m,_)) => n=m
	 | (App _,App _) => bug"UMtype_match;App"
	 | (Proj _,Proj _) => bug"UMtype_match;Proj"
	 | _ => false)
	   andalso
	   (for_all tmStk (ListUtil.zip(stkM,stkN))
	    handle Zip => false)
      end
  in
    tm (!LuosMode) (p1,p2) (e1,e2) (c1,c2) orelse (UVARS:= an; false)
  end
and UMtype_match c d = UMtm (Clos(c,[]),[]) (Clos(d,[]),[]);
(*************************************************
and UMtype_match c d = 
  let
    val an = !UVARS
    fun tm LMflg (M,N) =
      let
        val MN as (M,N) = (UMwhnf M,UMwhnf N)
        val _ = if !tm_debug
                  then (message"** UMtm_debug **";legoprint M;legoprint N)
                else ()
      in case MN
           of (Type i,Type j) => if LMflg then univ_leq i j
                                 else univ_equal i j
            | (Prop,Type j) => LMflg
            | (Prop,Prop) => true
            | (Rel n,Rel m) => n=m
            | (Ref(b1),Ref(b2)) => sameRef b1 b2
            | (App((f1,cs1),_),App((f2,cs2),_)) =>
                (tm LMflg (f1,f2)) andalso
                (for_all (tm LMflg)
                 (ListUtil.zip (cs1,cs2)) handle Zip => false)
            | (Bind((bt1,vs1),_,M1,M2),Bind((bt2,vs2),_,N1,N2)) =>
		bt1=bt2 andalso
		(case bt1 of
		   Pi =>
		     (!liberal_matching_switch orelse vs1=vs2) andalso
		     (tm false (M1,N1)) andalso tm LMflg (M2,N2)
		 | Sig =>
		     (tm LMflg (M1,N1)) andalso tm LMflg (M2,N2)
		 | Lda => (** ?? bug"UMtype_match; Lda"  **)
		     (tm false (M1,N1)) andalso tm LMflg (M2,N2)
		 | Thry => bug"UMtype_match: Thry"
		 | Let => bug"UMtype_match: Let")
            | (Proj(p1,c1),Proj(p2,c2)) =>
                (p1=p2) andalso (tm false (c1,c2)) (**?????????????**)
            | (Tuple(T1,ls1),Tuple(T2,ls2)) => 
                tm false (T1,T2) andalso
                (for_all (tm false)
                 (ListUtil.zip(ls1,ls2)) handle Zip => false)
            | (CnLst ls1,CnLst ls2) => 
                (for_all (tm false)
		 (ListUtil.zip(ls1,ls2)) handle Zip => false)
            | (Var(n,_),Var(m,_)) => n=m
            | _ => false
      end
  in
    tm (!LuosMode) (c,d) orelse (UVARS:= an; false)
  end;
********************************************)


(* compiling patterns *)
fun makePats c =
  let
    val _ = if not (!pat_debug) then ()
	    else (prs"**pat_deb; ";prnt_red c)
(* Conor *)
    fun splatDefs (Bind ((Let,Def),_,dfn,bod)) = splatDefs (subst1 dfn bod)
      | splatDefs (Bind (bv,nam,dom,rng)) = Bind (bv,nam,dom,splatDefs rng)
      | splatDefs x = x

    fun stripLocs mvars makeRhs =
      fn Bind((Lda,vis),n,lbl,bod) =>
           stripLocs (mvars+1) (fn x=> makeRhs (Bind((Lda,vis),n,lbl,x))) bod
       | CnLst pairs => (mvars,makeRhs,pairs)
       | _ => (prs"not a pattern: ";print_expand c;
	       failwith"not a pattern")
    val (mvars,makeRhs,pairs) = stripLocs 0 (fn x => x) (splatDefs c)
    val timestamp =  (* starts after the number of match vars *)
      let val ts = ref mvars
      in fn ()=> (ts:= succ (!ts); !ts)
      end
    val rec mp =
      (* The argument of type prntVisSort is because implicit arguments are
       * matched as "anonymous variables".  This is because of the inferred
       * arguments of the recursor of an inductive relation.  *)
	  fn (Rel n,_) => Pmv n
	   | (c,ShowNorm) =>
	       (case c of
		  App((f,aa),vs) =>
		    Papp(mp (f,ShowNorm),map mp (ListUtil.zip (aa,vs)))
		| Ref br => Pcons(br)
		| Prop => Pprop
		| Type n => Ptype(n)
		| c => (print_expand c;failwith"illegal pattern"))
	   | _ => Pmv (timestamp())
    val rec mpp =
      fn LabVT(RedPr,lhs,rhs)::rest =>
           let
	     val nlhs =
	       (if (!pat_norm_switch) then UMnorm else UMdnf) lhs
	     val _ = if not (!pat_debug) then ()
		     else (prs"**pat_deb:mpp, lhs ";print_expand nlhs)
	     val plhs = mp (nlhs,ShowNorm)
	     val (hc,args) = pat_head_const_args lhs plhs
	   in  (args,mvars,plhs,makeRhs rhs)::(mpp rest)
	   end
       | [] => []
       | _ => bug"makePats2"
  in
    mpp pairs
  end;

val add_reductions = HashReds.add_reductions o makePats;

end;  (* structure UMopen *)

open UMopen;

val dnf = UMdnf;
val type_match = UMtype_match;
val whnf = UMwhnf;
LegoFormat.whnfr:= whnf;

