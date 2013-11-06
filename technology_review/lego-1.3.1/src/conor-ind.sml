(*<TITLE>conor-ind.sml</TITLE>
<H2>conor-ind.sml</H2>

<XMP>
*)

functor FunConorInductiveNeeds(structure Namespace : NAMESPACE
			       structure Concrete : CONCRETE
			       structure Quartermaster : QUARTERMASTER
                               sharing type Quartermaster.cnstr_c =
                                            Concrete.cnstr_c)
  : CONORINDUCTIVENEEDS =
    struct
        exception bad_elim
	structure Concrete = Concrete
	local
	    open Concrete
	    fun bhead (Bind (_,_,h,_)) = h
	      | bhead _ = failwith "Bad bhead!"
	    fun btail (Bind (_,_,_,t)) = t
	      | btail _ = failwith "Bad btail!"
	    exception bad_term
           fun Ref_s s = #1 (fEval (Ref_c s));
           fun Ref_s2 s = #2 (fEval (Ref_c s));
           fun tagS [] = "EMPTY"
             | tagS [s] = s
             | tagS (h::t) = h^"_"^(tagS t)
	in
	fun define [] = ()
	  | define ((tag,v)::t) =
	    (let
		 val uv = unEval v
		     handle _ => raise bad_term
		 val _ = fEval uv
		     handle _ => raise bad_term
		 val vt  = type_of_constr v
                 val n = tagS tag
	     in
		 ((Quartermaster.Generate tag
                     (Let,Def,(UnFroz,Global),[],[n],uv));
		  prs ("Defining "^n^"\n");
		  define t)
	     end
	     handle bad_term =>
		 (((message
		    ("Could not generate "^(tagS tag)^"\n"));
		   (raise bad_term))
		  handle _ => define t) )
	    val normal = UMopen.UMnorm
	    fun app_synth f x = #1 (fEval (App_c (ShowNorm,unEval f,unEval x)))
	    fun elim_rule x = fEval (Quartermaster.Make [Ref_c x,Ref_c "elim"])


fun con_list n =
  let val names=
    (#deps
     ((fn (Bd x) => x)
      ((fn (Ref x) => x
         | _ => failwith "Bug in con_list (conor-ind.sml)")
       (Ref_s n))))
  in
    map (fn x => (x,Ref_s2 x)) names
  end

	    fun eq_info () =
		let
		    val (q1,qr,qu1) = Namespace.findConfig "Equality"
                 			 ("Eq","Eq_refl","Eq_subst")
		    val (q2,qu2,qs) = Namespace.findConfig "Qrepl"
                                         ("Eq","Eq_subst","Eq_sym")
		    val qr' = if q1=q2 then qr
			      else (q2^"_refl")
		in
		    {name = Ref_s q2,
		     refl = Ref_s qr',
		     sym = Ref_s qs,
		     subst = Ref_s qu2}
		    handle _ => failwith "Bad equality setup!"
		end
	    fun conflict_stuff () =
		let val (_,_,qu) = Namespace.findConfig "Equality"
                 			 ("Eq","Eq_refl","Eq_subst")
                    val (tv,fv,pv) = Namespace.findConfig "Theorems"
                                         ("trueProp","absurd",qu)
                    val (tv,fv,pv) = if pv="" then ("trueProp","absurd",qu)
                                              else (tv,fv,pv)
                in  {truth   = Ref_s tv,
                     falsity = Ref_s fv,
                     plan = Ref_s pv}
		end
		handle _ => failwith "Bad Theorems setup!"
	end
    end;

functor FunConorInductive(structure ConorInductiveNeeds :
			    CONORINDUCTIVENEEDS) : CONORINDUCTIVE =
    struct
	local
	    open ConorInductiveNeeds
	    open Concrete  

	    val Eq_a = ref Bot
	    val Eq_refl_a = ref Bot
	    val Eq_subst_a = ref Bot

	    fun Eq_subst (App ((q,[qt,qx,qy]),_)) qa l v =
		App ((!Eq_subst_a,qt::qx::qy::qa::l),
		     NoShow::NoShow::NoShow::ShowNorm::v)
	      | Eq_subst _ _ _ _ = failwith "Bad Eq_subst application"

	    fun bhead (Bind (_,_,h,_)) = h
	      | bhead _ = failwith "Bad bhead!"
	    fun btail (Bind (_,_,_,t)) = t
	      | btail _ = failwith "Bad btail!"

	    fun Ref_s name = #1 (fEval (Ref_c name))

	    (* de Bruijn hackers *)

	    (* ripped off from var_occur in term.sml *)
	    fun occur_rel p =
		fn Rel(p')        => p=p'
		 | App((c,cs),_)  => (occur_rel p c) orelse
		       (exists (occur_rel p) cs)
		 | Bind(_,_,c,d)  => (occur_rel (succ p) d) orelse
		       (occur_rel p c)
		 | Tuple(T,l)     => (occur_rel p T) orelse
		       (exists (occur_rel p) l)
		 | Proj(_,c)      => occur_rel p c
		 | _              => false

	    (* modified from above *)
	    fun touch_rel q =
		let
		    fun tr2 (Rel p) = Rel (p+q)
		      | tr2 (App ((c,cs),l)) = App ((tr2 c,map tr2 cs),l)
		      | tr2 (Bind (v,x,c,d)) = Bind (v,x,tr2 c,tr2 d)
		      | tr2 (Tuple (T,l)) = Tuple (tr2 T,map tr2 l)
		      | tr2 (Proj (n,c)) = Proj (n,tr2 c)
		      | tr2 x = x
		in
		    tr2
		end

	    fun insert_rel q =
		let
		    fun ir2 (Rel p) = Rel (if (p>=q) then (p+1) else p)
		      | ir2 (App ((c,cs),l)) = App ((ir2 c,map ir2 cs),l)
		      | ir2 (Bind (v,x,c,d)) =
			Bind (v,x,ir2 c,insert_rel (q+1) d)
		      | ir2 (Tuple (T,l)) = Tuple (ir2 T,map ir2 l)
		      | ir2 (Proj (n,c)) = Proj (n,ir2 c)
		      | ir2 x = x
		in
		    ir2
		end

	    fun min_list (n:int) [] = n
	      | min_list n (h::t) = min_list (if (h<n) then h else n) t
		
	    fun min_rel l u (Rel p) = if (p>l andalso p<u) then p else u
	      | min_rel l u (App((c,cs),_)) =
		min_list (min_rel l u c) (map (min_rel l u) cs)
	      | min_rel l u (Bind(_,_,c,d)) =
		min (min_rel l u c,(min_rel (l+1) (u+1) d)-1)
	      | min_rel l u (Tuple(T,elts)) =
		min_list (min_rel l u T) (map (min_rel l u) elts)
	      | min_rel l u (Proj(_,c)) =
		min_rel l u c
	      | min_rel _ u _ = u

	    local  (* manufactures nat_is_zero : nat->Prop etc *)
	    in
		fun test_definitions x =
		    let val {truth=truth,falsity=falsity,plan=_} =
                            conflict_stuff ()
                        val truthType = (!toc) truth
		        fun scheme_to_Prop_thing (Bind ((Pi,v),x,t,r)) =
		            Bind ((Lda,v),x,t,scheme_to_Prop_thing r)
                          | scheme_to_Prop_thing _ = truthType
                        fun con_term_to_tests (Bind ((Pi,v),x,t,r)) =
                            let val (tt,ff) = con_term_to_tests r
                            in  (Bind ((Lda,v),x,t,tt),Bind ((Lda,v),x,t,ff))
                            end
                          | con_term_to_tests _ = (truth,falsity);
                        fun list_tests _ [] = []
                          | list_tests (Bind ((_,_),_,ct,r)) (h::t) =
                            ((con_term_to_tests ct)::(list_tests r t))
                          | list_tests _ _ =
                            failwith "Bug in list_tests (conor-ind.sml)"
			val cl = con_list x
			val (erule,etype) = elim_rule x
			val pt = scheme_to_Prop_thing (bhead etype)
			val lt = list_tests
			    (normal (type_of_constr
				     (App ((erule,[pt]),[ShowNorm]))))
                            cl
			fun make_c_args c [] _ = []
			  | make_c_args c ((d,_)::t) ((tt,ff)::T)
			    = if (c=d) then tt::(make_c_args c t T)
			      else ff::(make_c_args c t T)
			  | make_c_args _ _ _ = failwith "test def cockup"
			fun all_tests [] = []
			  | all_tests ((h,_)::t)
			    = let
				  val rest = all_tests t
				  val args = pt::(make_c_args h cl lt)
				  val vis = map (fn _ => ShowNorm) args
			      in
				  ([x,"is",h],(App ((erule,args),vis)))::rest
			      end
		    in
			all_tests cl
		    end
	    end
local

    val count_args_res_type =
	let
	    fun cart n (t as (Ref _)) = (n,t)
	      | cart n (t as (App _)) = (n,t)
	      | cart n (Bind (_,_,_,r)) = cart (n+1) r
	      | cart _ _ =
		failwith "bug in count_args_res_type (conor-ind.sml)"
	in
	    cart 0
	end

    local
	fun any_in_list f [] = false
	  | any_in_list f (h::t) = f h orelse any_in_list f t
	fun any_rels n (Rel i) = (i>=n)
	  | any_rels n (App ((f,args),_)) = any_rels n f orelse
	                                    any_in_list (any_rels n) args
	  | any_rels n (Bind (_,_,t,r)) = any_rels n t orelse
	                                  any_rels (n+1) r
	  | any_rels _ _ = false
    in
	fun which_rel_args rt =
	    let
		fun do_list _ 0 = []
		  | do_list (Bind ((Pi,_),_,t,r))n =
		    if (occur_rel n rt) orelse any_rels 1 t
			then do_list r (n-1)
		    else (n::(do_list r (n-1)))
		  | do_list _ _ =
		    failwith "Bug in which_rel_args (conor-ind.sml";
	    in
		do_list
	    end
    end
    fun splice 0 _ = ([],[],1)
      | splice n w =
	if ((w<>[]) andalso (n=(hd w)))
	    then
		let
		    val (a1,a2,t) = splice (n-1) (tl w)
		in
		    ((t+1)::a1,t::a2,t+2)
		end
	else
	    let
		val (a1,a2,t) = splice (n-1) w
	    in
		(t::a1,t::a2,t+1)
	    end

    fun vis_list (App _) = []
      | vis_list (Ref _) = []
      | vis_list (Bind ((_,Vis),_,_,r)) = ShowNorm::(vis_list r)
      | vis_list (Bind ((_,Hid),_,_,r)) = NoShow::(vis_list r)
      | vis_list _ = failwith "bug in vis_list (conor-ind.sml)"

    fun scheme_to_con_arg_thing ca_type =
	let    
	    fun cat2 n (Ref _)  = touch_rel n ca_type
	      | cat2 n (App _)  = touch_rel n ca_type
	      | cat2 n Prop     = touch_rel n ca_type
	      | cat2 n (Type _) = touch_rel n ca_type
	      | cat2 n (Bind ((Pi,v),x,t,r)) =
		Bind ((Lda,v),x,t,cat2 (n+1) r)
	      | cat2 _ _ = 
		failwith "bug in scheme_to_con_arg_thing (conor-ind.sml)"
	in
	    cat2 0
	end

    fun con_term_to_dummy i _ Prop    = (Rel i)
(*    | con_term_to_dummy i (App _) _ = (Rel i)
      | con_term_to_dummy i (Ref _) _ = (Rel i)
      | con_term_to_dummy i (Rel _) _ = (Rel i)   *)
      | con_term_to_dummy i (Bind ((Pi,v),x,t,r))
	                    (Bind ((Pi,_),_,tf,rf)) =
	Bind ((Lda,v),x,t,con_term_to_dummy (i+1) r rf)
      | con_term_to_dummy _ x _ = ( (legoprint x);
	(failwith "bug in con_term_to_dummy (conor-ind.sml)") )

    fun con_term_to_con_arg i =
	let
	    fun cttca2 j _ Prop    = (Rel (i-j))
(*            | cttca2 j (Ref _) _ = (Rel (i-j))
	      | cttca2 j (App _) _ = (Rel (i-j))
	      | cttca2 j (Rel _) _ = (Rel (i-j))  *)
	      | cttca2 j (Bind ((Pi,v),x,t,r))
                         (Bind ((Pi,_),_,tf,rf)) = 
		Bind ((Lda,v),x,t,cttca2 (j-1) r rf)
	      | cttca2 _ x _ = ( (legoprint x);
		(failwith "bug in con_term_to_con_arg(conor-ind.sml)") )
	in
	    cttca2
	end

    fun make_param_types [] [] _ tr = []
      | make_param_types (h1::t1) (h2::t2) tr (Bind ((Pi,v),x,ty,r)) =
	if (h1=h2)
	    then ((Lda,Hid),x,touch_rel tr ty)::
		(make_param_types t1 t2 tr r)
	else ((Lda,Hid),"ix"^(string_of_num tr),touch_rel tr ty)::
	    ((Lda,Hid),"iy"^(string_of_num tr),touch_rel (tr+1) ty)::
	    (make_param_types t1 t2 (tr+1) r)
      | make_param_types _ _ _ _ =
	failwith "bug in make_param_types (conor-ind.sml)"

    fun touch_param_types 0 _ = []
      | touch_param_types n ((p,x,ty)::t) =
	(p,x,touch_rel n ty)::(touch_param_types (n-1) t)
      | touch_param_types _ _ =
	failwith "bug in touch_param_types (conor-ind.sml)"

    fun trick_type [] [] _ n = Rel (n-1)
      | trick_type (h1::t1) (h2::t2) ((_,x,ty)::tp) n =
	if (h1=h2) then trick_type t1 t2 tp n
	else Bind ((Pi,Vis),x^"eq",
		   App ((!Eq_a,
			 [touch_rel n ty,Rel (h1+n),Rel (h2+n)]),
			[NoShow,ShowNorm,ShowNorm]),
		   trick_type t1 t2 (tl tp) (n+1))
      | trick_type _ _ _ _ = 
	failwith "bug in trick_type (conor-ind.sml)"

    fun add_params rest =
	let
	    fun ap2 [] = rest
	      | ap2 ((b,x,t)::r) = Bind (b,x,t,ap2 r)
	in
	    ap2
	end

    fun build_injector s s_type =
	let
	    val (erule,etype) = elim_rule s_type
	    val c_list = map #1 (con_list s_type)
	    val (con,con_type) = fEval (Ref_c s)
	    val (na,rt) = count_args_res_type con_type
	    val wa = which_rel_args rt con_type na
	    val (args1,args2,_) = splice na wa
	    val vises = vis_list con_type
	    val term1 = App ((con,map Rel args1),vises)
	    val term2 = App ((con,map Rel args2),vises)
	    val source_type = type_of_constr term1
	    val param_types = make_param_types args1 args2 0 con_type
	    val param_qty = length param_types
	    val param_types_after = touch_param_types param_qty param_types
	    val hyp_type = App ((!Eq_a,[source_type,term1,term2]),
				[NoShow,ShowNorm,ShowNorm])
	    val (pred_ps,pred_vs) = (* proofs of injective equalities *)
		let                 (* with constructions of predecessors *)
		    val e_sn_list = ShowNorm::ShowNorm::
			(map (fn _ => ShowNorm) c_list)
		    fun pl2 [] [] _ _ = ([],[])
		      | pl2 (h1::t1) (h2::t2) w ((_,x,ty)::tp) =
			if (h1=h2) then pl2 t1 t2 w tp
			else
		    (*
 ********************
*)
  let
      val (rest_p,rest_v) = pl2 t1 t2 (tl w) (tl tp)
      val ty3 = touch_rel 3 ty
      val ty4 = touch_rel 4 ty
      val scheme = bhead etype
      val cat3 = scheme_to_con_arg_thing ty3 scheme
      val cat4 = scheme_to_con_arg_thing ty4 scheme
      val catfake = scheme_to_con_arg_thing Prop scheme
      val cat_rule = (normal (type_of_constr
			      (App ((erule,[cat3]),[ShowNorm]))))
      val catfake_rule = (normal (type_of_constr
				  (App ((erule,[catfake]),[ShowNorm]))))
      val cttd = con_term_to_dummy (h1+4)
      val cttca = con_term_to_con_arg (hd w) na
      fun pred_guts [] _ _ = [Rel 1]
	| pred_guts (hc::tc) (Bind 
			      (_,_,h_term,t_term))
                             (Bind 
			      (_,_,hf_term,tf_term)) =
	  ((if (hc=s) then cttca else cttd) h_term hf_term)::
		(pred_guts tc t_term tf_term)
	| pred_guts _ _ _ =
	  failwith 
	  "bug in pred_lists (conor-ind.sml)"
      val leib_thing =
	  Bind ((Lda,Vis),s^"_term",
		touch_rel 3 source_type,
		App ((!Eq_a,[ty4,Rel (h1+4),
			    App ((erule,cat4::
				  (pred_guts c_list cat_rule catfake_rule)),
				 e_sn_list)]),
		     [NoShow,ShowNorm,ShowNorm]))
      val refl_thing =
	  App ((!Eq_refl_a,[ty3,Rel (h1+3)]),[NoShow,ShowNorm])
  in
      ((Eq_subst (touch_rel 3 hyp_type)
		(Rel 3) 
		[leib_thing,refl_thing] 
		[ShowNorm,ShowNorm])::
       rest_p,
       ShowNorm::rest_v)
  end
(*
  ******************
                    *)
		      | pl2 _ _ _ _ =
			failwith "bug in pred_lists (conor-ind.sml)"
		in
		    pl2 args1 args2 wa param_types_after
		end
            val favourite_universe =
                case (whnf (!Eq_subst_a))
                 of  (Bind ((Lda,_),_,u,_)) => u
                  |  _ => Prop
	in
	    (add_params
	     (Bind ((Lda,Vis),s^"_hyp",hyp_type,
		    Bind ((Lda,Hid),"P",favourite_universe,
			  Bind ((Lda,Vis),s^"_trick",
				trick_type args1 args2 param_types_after 2,
				App ((Rel 1,pred_ps),pred_vs)))))
	     param_types)
	end

in

    fun make_inj_thms c_list type_name =
	let
	    val (t_term,t_type) = fEval (Ref_c type_name)
	in
	    (fn (Bind _) => []
	  | _ => let
		     fun it2 [] = []
		       | it2 ((h,_)::t) = ([type_name,h,"injective"],
					   build_injector h type_name)::(it2 t)
		 in
		     it2 c_list
		 end) t_type
	end

end

(* Clark inversion stuff *)

fun split_constructor (App ((_,tyl),vil)) = (0,[],tyl,vil)
  | split_constructor (Bind (_,_,t,r)) =
    let
	val (n',a',tyl',vil') = split_constructor r
    in
	(n'+1,t::a',tyl',vil')
    end
  | split_constructor _ = (0,[],[],[]);

(*
fun split_scheme (Bind (_,_,App ((_,tyl),_),Ref _)) = (0,[],tyl,vil)
  | split_scheme (Bind (_,_,_,Ref _)) = (0,[],[],[])
  | split_scheme (Bind (_,_,t,r)) =
    let
	val (n',a',tyl',vil') = split_scheme r
    in
	(n'+1,t::a',tyl',vil')
    end
  | split_scheme _ = (0,[],[],[]);
*)

(* should work for both---note dropped fourth elt in result tuple *)

fun split_scheme (Bind (_,_,App ((_,tyl),_),Ref _)) = (0,[],[],false)
  | split_scheme (Bind (_,_,t,r)) =
    let
	val (n',a',tyl',is_r) = split_scheme r
    in
	(n'+1,t::a',(Rel (n'+1))::tyl',is_r)
    end
  | split_scheme Prop = (0,[],[],true)   (* a bit grim *)
  | split_scheme _ = (0,[],[],false);

fun find_eq_places n old =
    let
	fun fep2 [] _ _ _ = old
	  | fep2 (hp::tp) (ht::tt) (h1::t1) (h2::t2) =
	    if (hp=n)
		then
		    let
			val old' = (fep2 tp tt t1 t2)
			val h = length old'
			val h1' = touch_rel (~h) h1
		    in
			((* message (string_of_num h);
			 legoprint h1;
			 legoprint h1';*)
			 (n,ht,h1',h2)::old')
		    end
	    else fep2 tp tt t1 t2
	  | fep2 _ _ _ _ = old
    in
	fep2
    end

fun make_rtyl_eq_holes 0 _ _ l = l
  | make_rtyl_eq_holes n [] d l = make_rtyl_eq_holes (n-1) d d l
  | make_rtyl_eq_holes n (h::t) d l =
    if (h=n) (* need to make a hole *)
	then make_rtyl_eq_holes n t d (map (insert_rel n) l)
    else make_rtyl_eq_holes n t d l;

fun atyl_shuffle n [] = []
  | atyl_shuffle n (h::t) = (insert_rel n h)::(atyl_shuffle (n+1) t);

fun make_atyl_eq_holes2 0 _ _ l = l
  | make_atyl_eq_holes2 n [] d (h::t) = h::(make_atyl_eq_holes2 (n-1) d d t)
  | make_atyl_eq_holes2 n (h::t) d l =
    if (h=n) (* need to shuffle l *)
	then Bot::(atyl_shuffle 1 (make_atyl_eq_holes2 n t d l))
    else make_atyl_eq_holes2 n t d l
  | make_atyl_eq_holes2 _ [] _ [] = [];

fun filterbot [] = []
  | filterbot (Bot::t) = filterbot t
  | filterbot (h::t) = h::(filterbot t);

fun make_atyl_eq_holes n d d' l = filterbot (make_atyl_eq_holes2 n d d' l);

fun con_branch_plan c_no name styl s_ttyl =
    let
	val (na,atyl,rtyl,rvil) = split_constructor (#2 (fEval (Ref_c name)))
	val depl = map (min_rel 0 (na+1)) rtyl
        val hrtyl = make_rtyl_eq_holes (na+1) depl depl rtyl (* make holes *)
	val hatyl = make_atyl_eq_holes (na+1) depl depl atyl (* make holes *)
	fun p2 0 _ = [(0,Rel 0,Rel (na+c_no+(length rtyl)),Rel 0)]
	  | p2 n (h::t) =
	    (n,Rel 0,h,Rel 0)::(find_eq_places n (p2 (n-1) t)
				depl s_ttyl hrtyl styl)
	  | p2 _ _ = []
	fun add_eq_refls n old =
	    let
		fun aer2 [] _ _ = old
		  | aer2 (hp::tp) (ht::tt) (h1::t1) =
		    if (hp=n)
			then
			    let
				val old' = (aer2 tp tt t1)
			    in
				(App ((!Eq_refl_a,[touch_rel (~na) ht,
						  touch_rel (~na) h1]),
				      [NoShow,ShowNorm]))::old'
			    end
		    else aer2 tp tt t1
		  | aer2 _ _ _ = old
	    in
		aer2
	    end
	fun solvep 0 = []
	  | solvep n = (Rel (n-na))::
	    (add_eq_refls n (solvep (n-1)) depl s_ttyl rtyl)
	val plan = find_eq_places (na+1) (p2 na hatyl) depl s_ttyl hrtyl styl
    in
	(plan,add_eq_refls (na+1) (solvep na) depl s_ttyl rtyl)
    end
fun con_branch_type is_r plan c_no name =
    let
(*	fun ins_rel_list q l = map (fn (a,b,c,d) => (a,b,insert_rel q c,d)) l*)
	fun cbt _ [(0,_,ty,_)] = ty
	  | cbt q ((n,Rel 0,ty,_)::t) =
	    Bind ((Pi,Vis),"a"^(string_of_num n),ty,cbt (q+1) t)
	  | cbt q ((n,ty,t1,t2)::t) =
	    Bind ((Pi,Vis),name^"_eq"^(string_of_num q),
		  App ((!Eq_a,[touch_rel (q+c_no) ty,
			      t1,touch_rel (q+c_no) t2]),
		       [NoShow,ShowNorm,ShowNorm]),
		  cbt (q+1) ((*ins_rel_list (n-1)*) t))
	  | cbt _ _ = failwith "bug in con_branch_type (conor-ind.sml)"
    in
	cbt (if is_r then 0 else 1) plan
    end

(* some edits here *)

fun arg_to_elim_rule c_list etype =
    let
	val scheme = bhead etype
	val (npar,party,resterm (* ,resvis *),is_r) = split_scheme scheme
	val (c_b_plans,solved_plans) =
	    let
		fun cbp _ [] = ([],[])
		  | cbp n (h::t) =
		    let
			val (h1,h2) = con_branch_plan n h resterm party
			val (t1,t2) = cbp (n+1) t
		    in
			(h1::t1,h2::t2)
		    end
	    in
		cbp 1 c_list
	    end
	fun con_branches n (h::t) (hp::tp) =
	    Bind ((Pi,Vis),h^"_branch",
		  con_branch_type is_r hp n h,
		  con_branches (n+1) t tp)
	  | con_branches n _ _ = Rel n
	fun add_params tail_end =
	    let    
		fun ap2 (Ref _) = tail_end
		  | ap2 (App _) = tail_end
                  | ap2 Prop    = tail_end    (* to cope with Relation *)
		  | ap2 (Bind ((Pi,v),x,t,r)) =
		    Bind ((Lda,v),x,t,ap2 r)
		  | ap2 _ = 
		    failwith "bug in arg_to_elim_rule (conor-ind.sml)"
	    in
		ap2
	    end
    in
	(add_params
	 (Bind ((Pi,Hid),"Phi",Prop,con_branches 1 c_list c_b_plans))
	 scheme,
	 solved_plans)
    end

fun make_con_term rel_pos solver =
    let
	fun mct2 n (Bind ((Pi,v),x,t,r)) =
	    Bind ((Lda,v),x,t,mct2 (n+1) r)
	  | mct2 n _ = App ((Rel rel_pos,
			     map (touch_rel n) solver),
			    map (fn x => ShowNorm) solver)
    in
	mct2 0
    end

fun check_can_do_theorems s =
    let
	fun c2 (Bind _) =
	    failwith "cannot apply Theorems to inductive families"
	  | c2 _ = ()
    in
	c2 (#2 (fEval (Ref_c s)))
    end

fun clark_inversion name =
    let
	val c_list = map #1 (con_list name)
	val (erule,etype) = fEval (Ref_c (name^"_elim"))
	val (elim_arg_1,solvers) = arg_to_elim_rule c_list etype
	val reduced_elim = normal (type_of_constr
				   (App ((erule,[elim_arg_1]),[ShowNorm])))
	fun con_terms n (h::t) (Bind ((_,_),_,ty,r)) =
	    (make_con_term n h ty)::
	    (con_terms (n-1) t r)
	  | con_terms _ _ _ = []
	val elim_args = elim_arg_1::(con_terms
				     (length c_list) solvers reduced_elim)
    in
	App ((erule,elim_args),map (fn x => ShowNorm) elim_args)
    end

	in
	    fun DoConorTheorems mytype =
		(let
		     val {name=name,refl=refl,subst=subst,...} = eq_info ()
		 in
		     (Eq_a := name);
		     (Eq_refl_a := refl);
		     (Eq_subst_a := subst)
		 end;
		 check_can_do_theorems mytype;
		 define (test_definitions mytype);
		 define (make_inj_thms (con_list mytype) mytype);
		 ())
	    fun DoConorInversion mytype =
		(let
		     val {name=name,refl=refl,subst=subst,...} = eq_info ()
		 in
		     (Eq_a := name);
		     (Eq_refl_a := refl);
		     (Eq_subst_a := subst)
		 end;
		 define [([mytype,"inversion"],clark_inversion mytype)];
		 ())
	end   
    end;	

(*
</XMP>
*)
