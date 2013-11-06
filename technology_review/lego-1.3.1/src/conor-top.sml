(*<TITLE>conor-top.sml</TITLE>
<H2>conor-top.sml</H2>

<XMP>
*)

use "conor-voodoo.sml";
use "conor-check.sml";

functor FunConorTopNeeds(structure Tactics : TACTICS
			 structure Toplevel : TOPLEVEL
			 structure Synt : SYNT
			 structure Namespace : NAMESPACE
			 structure ConorInductiveNeeds : CONORINDUCTIVENEEDS
			 sharing type
			         ConorInductiveNeeds.Concrete.cnstr_c =
			         Tactics.cnstr_c =
			         Toplevel.cnstr_c =
			         Synt.cnstr_c) : 
                                       CONORTOPNEEDS =
    struct
	local
	    open ConorInductiveNeeds.Concrete
	    open Tactics
	    open Toplevel
	    open Synt
	in
	    structure ConorInductiveNeeds = ConorInductiveNeeds
            structure Namespace = Namespace
	    exception cannot_do_intros
	    type inductive_info = {instance       : cnstr,
				   name           : string,
				   type_of_name   : cnstr,
				   param_types    : cnstr list,
				   param_vis      : visSort list,
				   constructors   : string list,
				   con_types      : cnstr list,
				   inst_params    : cnstr list,
				   inst_vis       : prntVisSort list,
				   ind_params     : cnstr list,
				   ind_vis        : prntVisSort list,
				   elim_rule      : cnstr,
				   elim_rule_type : cnstr,
				   elim_inst      : cnstr,
				   elim_inst_type : cnstr}

            exception not_inductive

	    local
		fun parse_app (Ref (Bd {bd=(_,s,_,_),...})) = (s,[],[])
		  | parse_app (App ((f,al),vl)) =
		    let
			val (s,bl,ul) = parse_app f
		    in
			(s,bl@al,vl@ul)
		    end
		  | parse_app _ = raise not_inductive
		    
		fun strip_params (Bind ((Pi,v),_,t1,r1))
                                 (Bind ((Pi,_),_,t2,r2)) =
		    if sameTerm t1 t2 then
			let
			    val (tl,vl) = strip_params r1 r2
			in
			    (t1::tl,v::vl)
			end
		    else ([],[])
		  | strip_params _ _ = ([],[])
		    
		fun split_this_many [] x = ([],x)
		  | split_this_many (_::t1) (h::t2) =
		    let
			val (t,x) = split_this_many t1 t2
		    in
			(h::t,x)
		    end
		  | split_this_many _ _ = raise Match

                fun mang_vis (Bind ((Pi,Hid),_,_,r)) (h::t) =
                             NoShow::(mang_vis r t)
                  | mang_vis (Bind (_,_,_,r)) (h::t) =
                             ShowNorm::(mang_vis r t)
                  | mang_vis x (h::t) = ShowNorm::(mang_vis x t)
                  | mang_vis _ [] = []
	    in
		fun get_inductive_info term =
		    let
			val this_instance = term
			val (this_name,argl,visl) = parse_app term
			val (type_ref,this_type_of_name) =
			    fEval (Ref_c this_name)
			val these_constructors =
			    (fn (Ref (Bd {deps=cl,...})) => cl
			  | _ => raise not_inductive) type_ref
			val these_con_types =
			    map (fn x => #2 (fEval (Ref_c x)))
			    these_constructors
			val (this_elim_rule,this_elim_rule_type) =
			    fEval (Ref_c (this_name^"_elim"))
			val (these_param_types,these_param_vis) =
			    strip_params this_type_of_name this_elim_rule_type
			val (these_inst_params,these_ind_params) =
			    split_this_many these_param_types argl
			val (these_inst_vis,these_ind_vis) =
			    split_this_many these_param_types visl
			val this_elim_inst =
			    App ((this_elim_rule,these_inst_params),
				 mang_vis this_elim_rule_type
                                          these_inst_params)
			val this_elim_inst_type = type_of_constr this_elim_inst
		    in
			{instance       = this_instance,
			 name           = this_name,
			 type_of_name   = this_type_of_name,
			 param_types    = these_param_types,
			 param_vis      = these_param_vis,
			 constructors   = these_constructors,
			 con_types      = these_con_types,
			 inst_params    = these_inst_params,
			 inst_vis       = these_inst_vis,
			 ind_params     = these_ind_params,
			 ind_vis        = these_ind_vis,
			 elim_rule      = this_elim_rule,
			 elim_rule_type = this_elim_rule_type,
			 elim_inst      = this_elim_inst,
			 elim_inst_type = this_elim_inst_type}:inductive_info
		    end
	    end

	    fun intros_t mygoal =
		((Intros mygoal true [""])
		 handle _ => raise cannot_do_intros;
		     let
			 val q = Ref (hd (Namespace.getNamespace ()))
		     in
			 (q,type_of_constr q)
		     end)

	    fun refine_t mygoal myterm =
		Refine mygoal 0 (unEval myterm)

	    fun replace_t mygoal (myterm,mytype) =
		replace mygoal (Cast_c ((unEval myterm),(unEval mytype)))

	    val conf_qrepl = Config_Qrepl
	    val addConfig = Namespace.addConfig
	    val findConfig = Namespace.findConfig
	    val isNewName = Namespace.isNewName
	    val define = ConorInductiveNeeds.define
	    val eq_info = ConorInductiveNeeds.eq_info
	    val getGoal = (#2) o goaln
            val tactic_wrapper = Namespace.tactic_wrapper
            fun checking_stuff comp =
		let
		    val (t,k,s) = Namespace.findConfig "Qnify"
                 			 ("","","")
                    val look = if comp then whnf
                               else (fn (x:cnstr) => x)
		in  if t<>"" then
		    {on = true,
                     name = #1 (fEval (Ref_c t)),
		     kill = #1 (fEval (Ref_c k)),
                     look = look}
                    else {on = false,name=Bot,kill=Bot,look=look}
		    handle _ => failwith "Bad Qnify setup!"
		end
            fun cnid (x:cnstr) = x
	    val q_look_hard = ref cnid
	    val q_rewrite = ref cnid
	end
    end;

functor FunConorTop(structure ConorTopNeeds : CONORTOPNEEDS) : CONORTOP =
    struct
	type cnstr_c = ConorTopNeeds.ConorInductiveNeeds.Concrete.cnstr_c
        type qtac = int->(cnstr*cnstr*cnstr*cnstr*cnstr)->int
	local
            val checking_on = ref false
            fun cnid (x:cnstr) = x
(*
	    val truePropProof = Bind((Lda,Hid),"P",Prop,
				     Bind((Lda,Vis),"p",Rel 1,Rel 1));
*)
	    fun get_head (Ref (Bd {bd=(_,s,_,_),...})) = s
	      | get_head (App ((f,_),_)) = get_head f
	      | get_head _ = failwith "Couldn't get type name!"
	    open ConorTopNeeds
	    open ConorInductiveNeeds
	    open Concrete
            structure ConorCheck =
                      ConorCheck (structure ConorTopNeeds=ConorTopNeeds)
            open ConorCheck
	    val Eq_a = ref Bot
	    val Eq_refl_a = ref Bot
	    val Eq_subst_a = ref Bot
	    val Eq_sym_a = ref Bot
	    fun lookupEq () =
		let
		    val {name=name,refl=refl,subst=subst,sym=sym} =
			eq_info ()
		in
		    (Eq_a := name);
		    (Eq_refl_a := refl);
		    (Eq_subst_a := subst);
		    (Eq_sym_a := sym)
		end
            fun Ref_s x = #1 (fEval (Ref_c x))
            val q_look_hard = ref cnid
            val q_rewrite = ref cnid
	    fun eqs_left2 (Bind ((Pi,_),_,dom,tail)) =
               (case (!q_look_hard) dom
                  of (App ((e,_),_)) =>
		     (if (sameTerm e (!Eq_a)) then 1 else 0) + (eqs_left tail)
                   | _ => eqs_left tail)
	      | eqs_left2 (Bind ((Pi,_),_,_,tail)) = eqs_left tail
	      | eqs_left2 _ = 0
            and eqs_left x = eqs_left2 ((!q_look_hard) x)
            fun ReadConfig comp =
                let
                    val stuff = checking_stuff comp
                    val _ = q_look_hard :=
                           (if comp then whnf else cnid)
                    val _ = q_rewrite := !q_look_hard
                    val _ = ConorCheck.check_stuff := stuff
                    val _ = checking_on := #on stuff
                in  ()
                end
	    exception not_an_eq
	    exception no_eqs_left
	    exception qtac_fail
	    fun parse_eq (term,equality as (App ((q,[t,x,y]),_))) =
		if q = (!Eq_a) then
		    let
			val qx = (!q_rewrite) x
			val qy = (!q_rewrite) y
			val new_eq = App ((!Eq_a,[t,qx,qy]),
					  [NoShow,ShowNorm,ShowNorm])
		    in
			(term,new_eq,t,qx,qy)
		    end
		else raise not_an_eq
	      | parse_eq _ = raise not_an_eq
	    fun next_eq goal n (term,itstype) =
		parse_eq (term,(!q_look_hard) itstype)
		handle not_an_eq =>
		    if ((n = 0) orelse ((eqs_left goal) = 0))
			then raise no_eqs_left
		    else next_eq goal n (intros_t (~9999))
	    fun QSilly n (q,qt,t,x,y) =
		(legoprint t;
		 legoprint x;
		 legoprint y;
		 raise qtac_fail)
	    fun QDummy n _ = if (n>0) then (n-1) else n
(*
	    fun QConflict n (q,qt,t,x,y) =
		let
		    val tn = get_head t
		    val xh = get_head x
		    val yh = get_head y
		    val clist = map (#1) (con_list tn)
		in
		    if ((xh=yh) orelse
			(not (member xh clist)) orelse
			(not (member yh clist)))
			then raise qtac_fail
		    else
			(refine_t (~9999)
			 (App ((!Eq_subst_a,
				[t,x,y,q,
				 (#1 (fEval (Ref_c (tn^"_is_"^xh)))),
				 truePropProof]),
			       [NoShow,NoShow,NoShow,
				ShowNorm,ShowNorm,ShowNorm])));
			0
		end
	    handle _ => raise qtac_fail
*)
            fun proveTrue (Bind ((Pi,v),s,t,r)) =
                Bind ((Lda,v),s^"haha",t,proveTrue r)
              | proveTrue _ = Rel 1
            fun QConflict n (q,qt,t,x,y) =
                let val info = get_inductive_info t
		    val tn = get_head t
		    val xh = get_head x
		    val yh = get_head y
                    val clist = #constructors info
                    val _ = if ((xh=yh) orelse
                                (not (member xh clist)) orelse
                                (not (member yh clist)))
                                then raise qtac_fail
                            else ()
                    val ip = #inst_params info
                    val iv = #inst_vis info
                    val tester = #1 (fEval (Ref_c (tn^"_is_"^xh)))
                    val thang = if (ip=[])
                                    then tester
                                else App ((tester,ip),iv)
                    val {truth = trueThing, falsity = _, plan = plan} =
                        conflict_stuff ()
                    val truthType = (!toc) trueThing
                in  if sameTerm plan (!Eq_subst_a)
                        then ((refine_t (~9999) 
                               (App ((!Eq_subst_a,
				[t,x,y,q,thang,proveTrue (normal trueThing)]),
			       [NoShow,NoShow,NoShow,
				ShowNorm,ShowNorm,ShowNorm])));0)
                    else ((refine_t (~9999)
                           (App ((plan,
                                  [App ((!Eq_subst_a,
                                   [t,x,y,q,
                                    Bind ((Lda,Vis),"trick",t,
                                        App ((!Eq_a,[truthType,
                                           App ((thang,[x]),[ShowNorm]),
                                           App ((thang,[Rel 1]),[ShowNorm])]),
                                          [NoShow,ShowNorm,ShowNorm])),
                                    App ((!Eq_refl_a,
                                           [truthType,
                                            App ((thang,[x]),[ShowNorm])]),
                                           [NoShow,ShowNorm])]),
                       [NoShow,NoShow,NoShow,ShowNorm,ShowNorm,ShowNorm])
                                  ]),[ShowNorm])));0)
                end
                handle _ => raise qtac_fail
	    fun QInject n (q,qt,t,x,y) =
		let
		    val tn = get_head t
		    val xh = get_head x
		    val yh = get_head y
		    val clist = map (#1) (con_list tn)
		    val eric = eqs_left (getGoal (~9999))
		in
		    if ((not (xh=yh)) orelse
			(not (member xh clist)) orelse
			(not (member yh clist)))
			then raise qtac_fail
		    else
			(refine_t (~9999)
			 (#1 (fEval (App_c (ShowNorm,
					    Ref_c (tn^"_"^xh^"_injective"),
					    unEval q)))));
			(if (n>=0) then (n+(eqs_left (getGoal (~9999)))-eric-1)
			 else n)
		end
	    handle _ => raise qtac_fail;

            fun occurs_check x y beef =
                (if (!checking_on)
                    then ((refine_t (~9999) (checking beef));0)
                 else raise no_cycle_proof)
                handle no_cycle_proof =>
                ((message "occurs check failure:");
                 (legoprint x);
                 (legoprint y);
                 (raise qtac_fail))

	    fun QSubst n (q,qt,t,x,y) =
		let
                    exception check_up of (cnstr*cnstr)
		    val sym_eq = App ((!Eq_sym_a,[t,x,y,q]),
				      [NoShow,NoShow,NoShow,ShowNorm])
		    val sym_eq_type = App ((!Eq_a,[t,y,x]),
					   [NoShow,ShowNorm,ShowNorm])
		    fun sub_eq (Ref (Bd {ts=i1,...})) (Ref (Bd {ts=i2,...})) =
			if (i1<i2) then (sym_eq,sym_eq_type)
			else if (i1>i2) then (q,qt)
			     else raise qtac_fail
		      | sub_eq (Ref (r1 as (Bd br1))) a2 = 
			if depends r1 a2
			    then raise check_up (sym_eq,sym_eq_type)
			else (q,qt)
		      | sub_eq a1 (Ref (r2 as (Bd br2))) =
			if depends r2 a1
			    then raise check_up (q,qt)
			else (sym_eq,sym_eq_type)
		      | sub_eq _ _ = raise qtac_fail
		in
		    ((replace_t (~9999) (sub_eq x y));
		     (if (n>0) then (n-1) else n))
                    handle (check_up beef) => occurs_check x y beef
		end
	    handle _ => raise qtac_fail
	in
	    fun Invert goal term =
		let
		    val (_,ty) = fEval term
		    val inv_thm = (get_head ty)^"_inversion"
		in
		    refine_t goal
		    (#1 (fEval (App_c (ShowNorm,Ref_c inv_thm,term))))
		    handle _ => failwith "I can't invert that!"
		end
	    val QTacList = ref [QSilly,QConflict,QInject,QSubst,QDummy]
	    fun Qnify comp n term_c =
		let
                    val _ = ReadConfig comp
		    fun tryQTacs n x =
			let
			    fun t2 ([]:qtac list) = n
			      | t2 (h::t) = h n x
				handle qtac_fail => t2 t
			in
			    t2
			end
		    fun DoQnify n term_c () =
			DoQnify (tryQTacs n
				 (next_eq (getGoal (~9999)
					   handle _ => raise no_eqs_left)
				  n (fEval term_c))
				 (!QTacList))
			Prop_c ()
			handle no_eqs_left => ()
		in
		    (lookupEq ());
                    (tactic_wrapper (DoQnify n term_c) ())
		end
	end
	local
	    open ConorTopNeeds
	    open ConorInductiveNeeds
	    open Concrete
	    val NSS = [NoShow,ShowNorm,ShowNorm]
	    fun copy_3_binds_and_define sym_name
		(Bind ((_,_),TN,T,
		       Bind ((_,_),un,u,
			     Bind ((_,_),vn,v,_)))) myterm =
		define
		[(sym_name,
		  Bind ((Lda,Hid),TN,T,
			Bind ((Lda,Hid),un,u,
			      Bind ((Lda,Hid),vn,v,myterm))))]
	      | copy_3_binds_and_define _ _ _ = failwith "Funny Eq_subst!"
	    fun makesym (q,qr,qu)=
		let
		    val Q = #1 (fEval (Ref_c q))
		    val QR = #1 (fEval (Ref_c qr))
		    val (QU,QUT) = fEval (Ref_c qu)
		in
		    copy_3_binds_and_define ([q,"sym"]) QUT
		   (Bind ((Lda,Vis),"my_eq",
(* equality *)	     App ((Q,[Rel 3,Rel 2,Rel 1]),NSS),
(* subst *)	     App ((QU,
(* params, eq *)      [Rel 4,Rel 3,Rel 2,Rel 1,
(* prop to sub *)      Bind ((Lda,Vis),"sly",Rel 4,
(* eq in prop *)        App ((Q,[Rel 5,Rel 1,Rel 4]),NSS)),
(* ref proof *)        App ((QR,[Rel 4,Rel 3]),[NoShow,ShowNorm])]),
		      [NoShow,NoShow,NoShow,ShowNorm,
                       ShowNorm,
                       ShowNorm])))
		end
	in
	    fun ConfigEquality (q,qr,qu) =
		((if isNewName (q^"_sym") then makesym (q,qr,qu) 
		  else ());
		      (addConfig ("Equality",q,qr,qu));
		      (conf_qrepl (q,qu,q^"_sym"));
		      message "Equality configured")
	    fun ConfigQnify (t,k,s) =
		((addConfig ("Qnify",t,k,s));
		      message "Qnify configured")
	    fun ConfigTheorems (t,f,p) =
		((addConfig ("Theorems",t,f,p));
		      message "Theorems configured")
	end
        local
            open Voodoo
	    open ConorTopNeeds
	    open ConorInductiveNeeds
	    open Concrete

type inductive_info = {instance       : cnstr,
                       name           : string,
		       type_of_name   : cnstr,
                       param_types    : cnstr list,
                       param_vis      : visSort list,
                       constructors   : string list,
                       con_types      : cnstr list,
                       inst_params    : cnstr list,
		       inst_vis       : prntVisSort list,
		       ind_params     : cnstr list,
		       ind_vis        : prntVisSort list,
                       elim_rule      : cnstr,
                       elim_rule_type : cnstr,
                       elim_inst      : cnstr,
                       elim_inst_type : cnstr}
(*
exception not_inductive

fun parse_app (Ref (Bd {bd=(_,s,_,_),...})) = (s,[],[])
  | parse_app (App ((f,al),vl)) =
    let
	val (s,bl,ul) = parse_app f
    in
	(s,bl@al,vl@ul)
    end
  | parse_app _ = raise not_inductive
*)
fun same_pi_depth (Bind ((Pi,_),_,t1,_)) (Bind ((Pi,_),_,t2,_)) =
    same_pi_depth t1 t2
  | same_pi_depth (Bind ((Pi,_),_,_,_)) _ = false
  | same_pi_depth _ (Bind ((Pi,_),_,_,_)) = false
  | same_pi_depth _ _ = true
(*
fun strip_params (Bind ((Pi,v),_,t1,r1)) (Bind ((Pi,_),_,t2,r2)) =
    if same_pi_depth t1 t2 then
	let
	    val (tl,vl) = strip_params r1 r2
	in
	    (t1::tl,v::vl)
	end
    else ([],[])
  | strip_params _ _ = ([],[])
*)
fun split_this_many [] x = ([],x)
  | split_this_many (_::t1) (h::t2) =
    let
	val (t,x) = split_this_many t1 t2
    in
	(h::t,x)
    end
  | split_this_many _ _ = raise Match

	    (************* dodgy dangle
	    fun dangle t = (((!toc) t);false) handle _ => true
            *******************)
	    fun orlist P [] = false
	      | orlist P (h::t) = (P h) orelse (orlist P t)

    fun Abstract name term_c =
	let
	    val (t,ty) = fEval term_c
	    val goal = getGoal (~9999)
	    val aswas = start goal
	    val vt = voo t
	    val vty = voo ty
            fun change v = if v=vt then Voo ("ab",1)
			   else raise voodoo_no_rewrite
	    val addab = ([(("ab",1),(Pi,Vis),name,vty)],
			 voorewrite change (#2 aswas))
	    val newgoal = stop addab
	    val refinebythis = (Bind ((Lda,Vis),"Phi",newgoal,
				    App ((Rel 1,[t]),[ShowNorm])))
	in
	    refine_t (~9999) (Bind ((Lda,Vis),"Phi",newgoal,
				    App ((Rel 1,[t]),[ShowNorm])))
	end

exception shes_not_there

fun get_name s =
    let
	fun gn2 n (Bind ((Pi,_),s',_,r)) =
	    if s=s' then n
	    else gn2 (n+1) r
	  | gn2 _ _ = raise shes_not_there
    in
	gn2 0
    end

fun get_num n =
    let
	fun gn2 k m (Bind ((Pi,_),w,_,r)) =
	    if (var_occur r) then gn2 (k+1) m r
	    else if m=n then k
		 else gn2 (k+1) (m+1) r
	  | gn2 _ _ _ = failwith
	    "there aren't that many (..)-> premises"
    in
	gn2 0 1
    end

fun search_goal (Ref_c s) 0 g = ((get_name s g)
				 handle shes_not_there =>
				     ((Abstract (s^"_ind") (Ref_c s));0))
  | search_goal term 0 g = ((Abstract "ind" term);0)
  | search_goal _ n g = get_num n g

fun grab_type 0 (Bind ((Pi,_),_,t,_)) = t
  | grab_type n (Bind ((Pi,_),_,_,r)) = grab_type (n-1) r
  | grab_type _ _ = failwith "bug: Conor can't count!"

fun do_enough_intros 0 = 0
  | do_enough_intros n =
    let
        val goal = getGoal (~9999)
	val info = get_inductive_info (grab_type n goal)
        val ip = (#inst_params info)
        fun needs_intro k = orlist (varn_occur k) ip;
        fun which 0 = []
          | which j = (needs_intro j)::(which (j-1))
        val which_ones = which n
        fun do_the_biz [] = n
          | do_the_biz (l as (h::t)) =
            if (orlist (fn x => x) l)
		then
		    let
			val (va,_) = intros_t (~9999)
                        val van = case va of
			              (Ref (Bd {bd=(_,s,_,_),...})) => s^"_ind"
                                    | _ => "ind_var"
                        val k = do_the_biz t
		    in
			case h of
			    false => ((Abstract van (unEval va));k)
			  | true => k-1
		    end
	    else n
    in
	do_the_biz which_ones
    end

(****************** old and dodgy
fun do_enough_intros 0 = 0
  | do_enough_intros n =
    let
        val goal = getGoal (~9999)
	val info = get_inductive_info (grab_type n goal)
    in
	if (orlist dangle (#inst_params info))
	    then ((intros_t (~9999));(do_enough_intros (n-1)))
	else n
    end
***********************)

fun needs_rewritten 0 [] = false
  | needs_rewritten 0 _ = true
  | needs_rewritten k ((Rel j)::t) = if k=j then needs_rewritten (k-1) t
				     else true
  | needs_rewritten _ _ = true

val no_deps = voofold true (fn _ => false)
    (fn a => fn b => a andalso b)

fun vargs (VRef _) = []
  | vargs (VApp ((f,al),_)) = (vargs f)@al
  | vargs _ = bug "bad type in Induction"
			    
fun vsub i j =
    voomap (fn k => if i=k then Voo j else Voo k)
	   
fun sel 1 (h::t) = h
  | sel n (h::t) = sel (n-1) t
  | sel _ [] = bug "bad list select"

fun do_rewriting pos goal (info:inductive_info) =
    let
        val inst_par = (#inst_params info)
	val n_par = length (#ind_params info)
	val {name=qname,refl=qrefl,subst=_,sym=_} =
	    eq_info ()
	val v_eq = voo qname
	val v_eq_refl = voo qrefl
	val (old,P) = introvoo "R" 1 (introvoo "x" pos (start goal))

(*
   (old                                                     ,   P)
    {x1:u1}..{x(n-1):u(n-1)}{R1:Ind m1[x..]..m(n_par)[x..]}     P
*)


	(* grab new prefix from elim rule *)
	local
	    val (_,vtail) = introvoo "junk"
		(1+(length (#constructors info)))
		(start (#elim_inst_type info))
	in
	    val elim_tail = introvoo "rel" 1
		            (introvoo "y" n_par ([],vtail))
	end

(*
   elim_tail
   {y1:w1}..{y(n_par):w(n_par)}{rel1:Ind y1..y(n_par)}    who cares?
*)

	(* this stuff is for dep equalities *)
	val par_deps = deple (#1 elim_tail)
	local
	    fun ms2 [] = bug "empty make_sigma"
	      | ms2 (h::t) =
		let
		    val (_,_,s,u) = fetch h elim_tail
		in
		    if t=[] then ([],u)
		    else let
			     val (vc,vt) = ms2 t
			 in
			     ((h,(Sig,Vis),s,u)::vc,vt)
			 end
		end
	in
	    fun make_sigma l = voo (stop (ms2 l))
	end
	fun make_tuple t f [i] = f i
	  | make_tuple t f l = VTuple (t,map f l)
	
	(* glue on new prefix *)
	val step1 = ((#1 elim_tail)@old,P)

(*
   step1
   {y1}..{y(n_par)}{rel1:Ind y1..}{x1}..{x(n-1)}{R1:Ind m1..}   P
*)

	(* pick out args from old relation *)
	val (_,oldargs) = split_this_many inst_par
                          (vargs (#4 (fetch ("R",1) step1)))
	(* now work out which ones to sub *)
	fun elideargs _ [] S = S
	  | elideargs i ((Voo ("x",j))::t) S =
	    let
		val (_,_,s,u') = fetch ("x",j) S
		val (_,b,_,u) = fetch ("y",i) S
		val newi = (("y",i),b,s,u)
	    (* we rename yi with xj's name *)
	    in
		if (no_deps u') orelse u'=u
		    then
			let
			    val cut_it = elide ("x",j) S
			    val sub_it =
				sub ("x",j) (Voo ("y",i))
				cut_it
			    val newS = swap newi sub_it
			    val t' = map (vsub ("x",j)
					  ("y",i)) t
			in
			    elideargs (i+1) t' newS
			end
		else elideargs (i+1) t S
	    end
	  | elideargs i (h::t) S =
	    elideargs (i+1) t S
	(* do the elisions *)
	val step2 = elideargs 1 oldargs step1

(*
   step2
   {y1}..{y(n_par)}{rel1:Ind y1..}{x?}..{x?}{R1:Ind newargs}   P
*)

	(* pick out the new args *)
	val (_,newargs) = split_this_many inst_par
                          (vargs (#4 (fetch ("R",1) step2)))
	(* now work out the equalities *)
	fun narg (_,i) = sel i newargs

(*      WRONG!!!
	fun inseq _ [] S = S
	  | inseq i ((Voo ("y",_))::t) S =  (* what if it's not yi? *)
	    inseq (i+1) t S
	  | inseq i (h::t) S =
	    let
		val i_deps = par_deps ("y",i)
		val q_t = make_sigma i_deps
		val q_lhs = make_tuple q_t Voo i_deps
		val q_rhs = make_tuple q_t narg i_deps
		val (_,_,s,_) = fetch ("y",i) S
		val vq = (("q",i),(Pi,Vis),s^"_eq",
			  VApp ((v_eq,[q_t,q_lhs,q_rhs]),
				[NoShow,ShowNorm,ShowNorm]))
	    in
		inseq (i+1) t (shove vq ("rel",1) S)
	    end
*)

	fun inseq _ [] S = S
	  | inseq i (h::t) S = if (h <> (Voo ("y",i))) then
	    let
		val i_deps = par_deps ("y",i)
		val q_t = make_sigma i_deps
		val q_lhs = make_tuple q_t Voo i_deps
		val q_rhs = make_tuple q_t narg i_deps
		val (_,_,s,_) = fetch ("y",i) S
		val vq = (("q",i),(Pi,Vis),s^"_eq",
			  VApp ((v_eq,[q_t,q_lhs,q_rhs]),
				[NoShow,ShowNorm,ShowNorm]))
	    in
		inseq (i+1) t (shove vq ("rel",1) S)
	    end
            else inseq (i+1) t S
	(* now do the equalities *)
	val step3 = inseq 1 newargs step2
	(* now sub for and elide the old rel *)
	val step4 = sub ("R",1) (Voo ("rel",1))
	    (elide ("R",1) step3)

(*
   step4
   {y1}..{y(n_par)}{rel1:Ind y1..} {x?}..{x?}           P
                          & mix in {q?:y?=m'[x..]}..
*)

	(* now get new goal *)
	val newgoal = stop step4
	val _ = message "Induction rewrites goal:"

	(* next build the proof that rewrite is ok *)
	(* get old pis and make them lambdas *)
	val old' = map (fn (i,(_,v),s,t) => (i,(Lda,v),s,t)) old
	(* tack on proof of new goal *)
	val ldas = (("Phi",1),(Lda,Vis),"Phi",voo newgoal)::old'

(*
   ldas
   [Phi:newgoal][x1]..[x(n-1)][R1:Ind m1..]
*)

	(* get the stuff after the rel *)
	fun chop ((i,_,_,_)::t) = if i=("rel",1) then t else chop t
	  | chop [] = bug "induction rewrite proof flaw"
	(* fill in blanks / prove equalities *)
	val tail_end = chop (#1 step4)

(*
    tail_end   (need to make proof of these)
    {x?}..{x?} mixed with {q?:y?=m'}..
*)

(*
   we fill an x gap with an x var
   and prove an equality by reflexivity with the old arg (ie m[x1..])
*)

	fun oarg (_,i) = sel i oldargs
	fun pf [] = []
	  | pf ((("x",j),_,_,_)::t) = (Voo ("x",j))::(pf t)
	  | pf ((("q",i),_,_,VApp ((_,[u,y,z]),_))::t) =
	    let
		val i_deps = par_deps ("y",i)
		val q_term = make_tuple u oarg i_deps
	    in
		(VApp ((v_eq_refl,[u,q_term]),[NoShow,ShowNorm]))::(pf t)
	    end
	  | pf _ = bug "induction rewrite proof prob"
	val proof_args = oldargs@[Voo ("R",1)]@(pf tail_end)
	fun viss [] = []
	  | viss ((_,(_,Vis),_,_)::t) = ShowNorm::(viss t)
	  | viss ((_,(_,Hid),_,_)::t) = NoShow::(viss t)
	  | viss _ = bug "bad visibility in induction"
	val visibilities = viss (#1 step4)
	val proof_tail = VApp ((Voo ("Phi",1),proof_args),visibilities)
	(* put it all together *)
	val vproof = (ldas,proof_tail)

(*
   vproof
   [Phi:{y1}..{y(n_par)}{rel:Ind y1..}{x?}&{q?:y?=m'?}P]
                                               [x1]..[x(n-1)][R1:Ind m1..]
     Phi m1..m(n_par)    R1            x? & (Eq_refl m?)
*)

	val _ = refine_t (~9999) (stop vproof)
	val goalnow = getGoal (~9999) (* should be same as newgoal *)
    in
	(n_par,goalnow,get_inductive_info (grab_type n_par goalnow))
    end

fun NewInduction term num =
    let
	val oldgoal = getGoal (~9999)
	val pos' = do_enough_intros (search_goal term num oldgoal)
	val goal' = getGoal (~9999)
	val info' = get_inductive_info (grab_type pos' goal')
	val (pos,goal,info) = if needs_rewritten pos' (#ind_params info')
				  then do_rewriting pos' goal' info'
			      else (pos',goal',info')
	val vgoal =                             introvoo "rel" 1
	                      (introvoo "y" pos
		   (start goal))
	val C_type = (fn (Bind ((Pi,_),_,t,_)) => t
		       | _ => raise Match) (#elim_inst_type info)
	val (C_pars,C_rest) = introvoo "y" pos (start C_type)

(* need to check kind of elim rule:
   either Relation    {C:{y1}..{y(pos)}Prop}
       or otherwise   {C:{y1}..{y(pos)}(Ind y1..)->Type}
*)

        val (prefix,suffix) = case C_rest
	    of (VBind ((Pi,v),_,_,_)) =>
		let
		    val (_,_,s,t) = fetch ("rel",1) vgoal
		in
		    swap (("rel",1),(Lda,v),s,t) vgoal
		end
	  | _ => elide ("rel",1) vgoal
	
(*
  now prefix has the right bound vars for arg to elim rule, but pi bound,
  so swap to lambda binding and fix the visibilities to conform to elim rule
*)

	fun do_ldas t [] = t
	  | do_ldas ((i,_,s,u)::t1) ((_,(_,v),_,_)::t2) =
	    (i,(Lda,v),s,u)::(do_ldas t1 t2)
	  | do_ldas _ _ = bug "bad elim rule handling"
	val elim_arg = (do_ldas prefix C_pars,suffix)

(*
  elim_arg
  [y1]..[y(pos)] (if needed [rel1:Ind y1..])   P
*)

	val eliminator = App ((#elim_inst info,[stop elim_arg]),
			      [ShowNorm])
	val _ = refine_t (~9999) eliminator
    in
	()
    end
	in
	    fun Induction v d =
		if (Namespace.activeProofState ())
		    then
			(tactic_wrapper (fn () => NewInduction v d) ())
			handle not_inductive => failwith
			           "no induction principle"
			     | missing_voodoo => failwith
				   "too hard for Induction tactic"
		else failwith "No refinement state"
        end
    end;

(*
</XMP>
*)
(*
structure NCT = FunConorTop(structure ConorTopNeeds=ConorTopNeeds)
open NCT
*)
