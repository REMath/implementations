(* top level *)

val pr_debug = ref false;
val dummy_time = check_timer(start_timer())

functor FunToplevel
    (structure Namespace:NAMESPACE
     structure Machine:MACHINE
     structure Concrete:CONCRETE
     structure Synt:SYNT
     sharing type Synt.cnstr_c=Concrete.cnstr_c
     and type Namespace.question=Synt.question) (* : TOPLEVEL *) =
struct
  type cnstr_c=Concrete.cnstr_c

(* toplevel goal: save for use at end of proof *)
val TLGOAL = ref Bot;
val TLNAME = ref ("",Global);
val TLTIMER = ref (start_timer())

(* initialize toplevel *)
val init_toplevel = Namespace.init_history

(* Putting PR and DECH together is ugly; but it's the only way I
 * can get "auto discharge".  Notice DECH is now hidden from users *)
fun Pr() = 
  let 
    fun DECH () =
      case (Namespace.getCurrentGoals()) of   (* discharge function *)
	Namespace.Unknown([])::q  => (Namespace.DECH(); DECH())
      | Namespace.Push(n,m,c)::q  =>  (Namespace.DECH(); DECH())
      | Namespace.Unknown(_)::_  => PR()
      | []  => (Namespace.DECH(); Pr())
  in
    case (Namespace.getCurrentGoals()) of
      [] =>
	let
	  open Concrete
	  open Namespace
	  val pt = UMpnf (getProofTerm())   (* UMpnf ?? *)
	  val cpt = if pure pt then unEval pt else bug"Pr:impure proof"
	  val refine_time = check_timer(!TLTIMER)
	  val com = snd (fEval cpt)
	  val retype_time = check_timer(!TLTIMER)
	  val recheck = par_tm com (!TLGOAL)
	  val recheck_time = check_timer(!TLTIMER)
	  val _ = if (!pr_debug) then
	    (prs("**pr_deb: refin "^mks_time refine_time^
		 " retyp "^mks_time(sub_time(retype_time,refine_time))^
		 " rechk "^mks_time(sub_time(recheck_time,retype_time)));
	     if earlier(refine_time,sub_time(recheck_time,refine_time))
	       then message" !!!!"
	     else message"")
		  else()
	in
	  if recheck
	    then (pushHistProven (!TLNAME,(pt,!TLGOAL));
		  message("*** QED ***   (* "^
			  makestring_timer (!TLTIMER)^" *)"))
	  else bug"Pr"
	end
    | Namespace.Push(_)::_     => DECH()
    | Namespace.Unknown([])::q => DECH()
    | Namespace.Unknown(l)::q  => if interactive() then prl l else ()
  end

and PR() = let
	       open Namespace
	   in
	       if activeProofState()
		   then ((if interactive()
			     then 
				 (if isAnnotating() then 
					message "\250 Start of Goals \251" else ();
				  prt_context_ref	
				 (hd (getContextBeforeProof())) ElideDfns)
			 else ());	
			 Pr();
			 (if isAnnotating() then message "\250 End of Goals \251" 
				else ()))
	       else if provenState() 
			then message"all goals proven!"
		    else failwith"No refinement state"
	   end;


(* to apply tactics *)
fun appTac f x =
    if not (Namespace.activeProofState()) then failwith"no active goals"
    else Namespace.tactic_wrapper (fn () => ((f x);())) ();

fun AppTac f x = (appTac f x; PR())
fun smallAppTac f x = (appTac f x;  
		       if isAnnotating() then PR() else Pr());


fun Goal u (namLocGlob as (nam,_)) =
  if Namespace.activeProofState()
    then failwith"Cannot use 'Goal' during a proof"
  else if nam<>"" andalso (not (Namespace.isNewName nam))
	 then failwith("\""^nam^"\" already in namespace")
  else let val (V,T) = Concrete.fEval u
	   val V = UMpnf V             (**  UMpnf ??  **)
       in  if kind T then (message("Goal "^nam);
			   Namespace.Goal V;
			   TLGOAL:= V;
			   TLNAME:= namLocGlob;
			   TLTIMER:= start_timer();
                           if isAnnotating() then PR () else Pr ())
	   else failwith"Only a Prop or a Type can be a goal"
       end;


fun UNDO n = if Namespace.proofState()
	       then (Namespace.Undo n; message "Undo"; PR())
	     else failwith"Cannot undo: not in proof state";


fun nullTac (x:substitution) = ();

val AutoTac = ref nullTac;


fun solve tacflg g (nsp,new,c,q,close,V) tac =
   (if not tacflg
	then (print_refine g V; Namespace.pushHist(); ())
    else ();

    (*** This is UNSAFE and should be integrated in namespace.sml ***)
	Namespace.putNamespace nsp;
	Namespace.putProofTerm c;
	Namespace.putCurrentGoals q;

	close(); tac new;
    if not tacflg then (if isAnnotating() then PR() else Pr()) else ())

and RefineTac_c n m v_c = solve true n (Synt.resolve_c n m v_c)
and RefineTac_a n m v = solve true n (Synt.resolve_a n m v)
and Refine n m v_c = solve false n (Synt.resolve_c n m v_c) (!AutoTac)
and SolveTacn n m v_c =
    let val (res as (_,new,_,_,_,_)) =
      ((Synt.resolve_c n m v_c) handle _ => ([],[(0,Bot)],Bot,[],(fn()=>0),Bot))
    in  
      if new=[] then (solve true n res nullTac; true) else false 
    end;


fun KillRef() = (Namespace.killRef(); message "KillRef: ok, not in proof state");


fun Claim v_c =
  let
    val (mkVar,eraseNew,close) = Namespace.manageVars()
    val ((V,T),sbst) = Concrete.EvalRefine Synt.type_of_Var mkVar v_c
  in
    if kind T
      then (Namespace.Claim V sbst mkVar eraseNew close;
	    prs"Claim  "; legoprint V;
	    if isAnnotating() then PR() else Pr())
    else failwith"Only a Prop or a Type can be claimed"
  end



val Next = appTac (fn n => (Namespace.NextTac n; message("Next "^string_of_num n)));

val intros_debug = ref false;
fun IntrosTac n l hnfFlg = (Namespace.NextTac n; Namespace.do_intros 0 l (hnfFlg,l=[]))
fun Intros n hnfFlg =
      smallAppTac
        (fn l => let
		   val show_l = concat_sep " " (map (fn "" => "_" | x => x) l)
		   val _ = if (!intros_debug)
			     then (prs"**intros_debug** "; pri n; prs" ";
				   prs show_l; prs" "; print hnfFlg; line())
			   else ()
		   val count = IntrosTac n l hnfFlg
		 in
		   prs(if hnfFlg then "Intros " else "intros ");
		   prs"("; pri count; prs") "; message show_l;
		   if interactive() andalso not (isAnnotating())
		       then Namespace.prt_context_dpth count ElideDfns
		   else ()
		 end);

val Save_frz_default = ref UnFroz
end
