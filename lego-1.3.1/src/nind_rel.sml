(* <TITLE>nind_rel.sml</TITLE>
<H2>nind_rel.sml</H2>

<XMP>
*)

(* This is Conor's version, with fabbo inductive hypotheses. *)

functor FunRelation (structure Concrete:CONCRETE
		     structure Inductive:INDUCTIVE
		     structure Namespace:NAMESPACE
		     sharing type Concrete.cnstr_c=Inductive.cnstr_c)
     : RELATION =
    struct
	local
	    open Concrete
	    open Inductive
	    open Namespace
	in
	    type cnstr_c=cnstr_c
(* New version which produces non-dependent elimination rules *)
(* What do I mean by non-dep. elim rules ???
[Even_elim : {T:nat->Type}
             (T zero)->
             ({n:nat}(T n)->T (suc (suc n)))->
                   {n:nat}(Even n)->T n];
These are the two rules for even.....note in particular that for the
non-dep form we need to know the instantiation of the last part of
ev2, i.e. the +2 part. Also tricky is that as deep as phizero, we
have to change what C_even is applied to! 

{T:{x1|nat}(Even x1)->Type}
       (T ev1)->
       ({n:nat}{x1:Even n}(T x1)->T (ev2 n x1))->
      {x1|nat}{z:Even x1}T z

ev2:{n,m:nat}({k:nat}(Even n (m+k))) -> Ev*****

*)
(* ind_relations.sml *)

(* tidying up code -- no major changes *)

(* Modified version of datatype.sml to get something for inductive
   relations *)

(* Signature of this module is the function do_inductive_type which takes
   3 ctxt_c lists and a boolean and returns a ctxt_c list
   paired with a reduction   *)

(* schema_head is not just a string, but a string
   applied to some arguments.... *)


fun nT_of_C l str typestr= 
  fold  (fn ((a,b,v),x) => Bind_c((Pi,v,(UnFroz,Local),[],[a],b),x))
   l (Prop_c);

 (* Changed (typestr) to (Prop_c) in above function, so that 
    elimination is only over Prop, no matter what you set TYPE and
    typestr to be.....*)          
(* The type of ``C'' for an inductive type str with binders l *)

fun nstart_A_of_C l str = 
   foldl  (fn x => (fn (a,_,b) => App_c((prVis b),x,Ref_c(a))))
   (Ref_c("C_"^str)) l;

(* Conor hacked nUniver_of_C to hide the relation parameters in the
   conclusion of the elim rule, ie
      {x1|p1}...{xn|pn}(R x1 ... xn)->(C_R x1 ... xn)
   instead of
      {x1:p1}...{xn:pn}(R x1 ... xn)->(C_R x1 ... xn)                *)

fun nUniver_of_C l str =           (* This Hid used to be v (sez Conor) *)
  foldr (fn (a,b,v) => (fn x => Bind_c((Pi,Hid,(UnFroz,Local),[],[a],b),x)))
  (Bind_c((Pi,Vis,(UnFroz,Local),[],["z"],(start_T_of_C l str)),
            (nstart_A_of_C l str)))  l;

fun app_of_schema_applied (Head(s)) z = z |
    app_of_schema_applied (Appl_a(x,a,c)) z =
    App_c(x,(app_of_schema_applied a z),c);

fun nphizero (Ref_s(s)) z = app_of_schema_applied s 
                     (Ref_c("C_"^(get_name_app s)))
  | nphizero (Bind_s((Pi,x,_,_,l,c),c1)) z =
                     Bind_c((Pi,x,(UnFroz,Local),[],l,c),
                 (nphizero c1 z))
  | nphizero _ z = raise sch_err "Schema is not strictly positive";
(* Need to change this!!!! *)		     

(* Conor hacked nphihash to compensate for the hidden parameters in the
   conclusion of the elim rule                                       *)

fun nphihash (Ref_s(s)) f z = App_c(ShowNorm,(*(app_of_schema_applied s f)*)
                                             (* Conor hacks again *)f,z)
   |nphihash (Bind_s((Pi,x,_,_,l,c),c1)) f z =
            Bind_c((Lda,x,(UnFroz,Local),[],l,c),
                      (nphihash c1 f (gen_app z x l))) |
       nphihash _ f z = raise sch_err "Schema is not strictly positive";

fun get_head (Ref_s(s)) = s |
    get_head (Bind_s(_,s)) = get_head(s) |
    get_head (Bind_sc(_,s)) = get_head(s) ;  

fun nstart_up S z str ty = let val s = get_head S in
    app_of_schema_applied s ((Ref_c("C_"^(get_name_app s)))) end;

(* `nonarities' is Claire's function to filter out the inductive
   hypotheses we want to keep; we want to use `binders' instead,
   so that we get all the arguments to the constructor            *)

fun nonarities (Ref_s(_)) = [] |
    nonarities (Bind_s((_,y,_,_,l,s1),s)) = 
      (map (fn x => (x,y,s1)) l)@(nonarities s) |
    nonarities (Bind_sc(_,s)) = (nonarities s);

(* observe we replace `nonarities' with `binders' in thetazero *)

fun nthetazero S z =
  let 
    val l1 = (* nonarities *) binders S;      (* Conor's alteration *)
      val (name,ty) = get_name_and_type S;
    val l2 = arities S
  in
    let val begin = foldr 
      (fn (str,x,schema) =>
       (fn so_far => Bind_c((Pi,x,(UnFroz,Local),[],[str^"_ih"],
			     (nphizero schema (Ref_c(str)))),
			    so_far)))
      (nstart_up S z name ty)
      l2
    in 
      foldr (fn (name,x,cnstr) =>
	     (fn so_far => Bind_c((Pi,x,(UnFroz,Local),[],[name],cnstr),so_far)))
      begin
      l1
    end 
  end;
		    
fun neliminator schema_names name type_of_name list_of_schemas typestr =
    let val name_l = binders_ind type_of_name;
	val start_value = nUniver_of_C name_l name;
	val innerpart =
	  (foldr (fn (str,schema) =>
		  (fn rest => Bind_c((Pi,Vis,(UnFroz,Local),[],[""],
				      (nthetazero schema str)),rest)))
	   start_value 
	   list_of_schemas)
    in
      foldr (fn (str,cnstr) =>
	     (fn rest => Bind_c((Pi,Vis,(UnFroz,Local),[],["C_"^str],
				 (nT_of_C (binders_ind cnstr) str typestr)),
				rest)))
      innerpart
      schema_names
    end;

fun neliminators schema_names list_of_schemas typestr =
  map (fn (str,cnstr) => 
       (Lda,Vis,(UnFroz,Global),[],[str^"_elim"],
	(neliminator schema_names str cnstr list_of_schemas typestr))(*:binder_c*))
  schema_names;
  
(* Need to elaborate ``schema_names'' so as to retain the
   type information from which derives type of ``C'' *)

(* Need something to force an argument into every Pi binding
   in a schema else create one... *)

fun nfirst_bindings name_list typestr = 
   map (fn (str,cnstr) => 
    (Lda,Vis,(UnFroz,Local),[],["C_"^str],
     (nT_of_C (binders_ind cnstr) str typestr))(*:binder_c*)) name_list;

fun nsecond_bindings schema_list =
    map (fn (str,schema) =>  
    (Lda,Vis,(UnFroz,Local),[],[mkNameGbl("f_"^str)], 
     (nthetazero schema str))(*:binder_c*))
    schema_list;

fun nall_bindings name_list schema_list typestr =
   (nfirst_bindings name_list typestr) @ (nsecond_bindings schema_list) @
   (third_bindings schema_list);

(* takes a constructor name and its schema and gives back
   what Luo calls ``\iota(bar{a})'', a cnstr_c '' *)

(* Should have eliminated the rev by using foldl...check this ! *)


fun nrecursor_applied_to_bindings name_list schema_list (x,S) =
  let val (str,ty) = get_name_and_type S
  in
     (foldl (fn cnstr => (fn (name,schema)
			  => (App_c(ShowNorm,cnstr,Ref_c(mkNameGbl("f_"^name)))))) 
      (foldl (fn cnstr => (fn (name,cnstr2) =>
			   (App_c(ShowNorm,cnstr,Ref_c("C_"^name)))))
       (Ref_c((str)^"_elim")) name_list)
      schema_list)
  end;

(* Conor's mangling means the reductions are shafted...
fun nlhs_of_reduction name_list schema_list (x,S) =
  (* Apply first the arguments given in the schema head and then iota  *)
   App_c(ShowNorm,
        (app_of_schema_applied (get_head S)
	(recursor_applied_to_bindings name_list schema_list (x,S))),
        (iota_of_a(x,S)))
	;

fun nrhs_of_reduction name_list schema_list (x,S) =
  foldl 
  (fn cnstr =>
   (fn (name,y,schema) =>
    App_c((prVis y),cnstr,(nphihash schema   
			   (nrecursor_applied_to_bindings
			    name_list schema_list (name,schema))
			   (Ref_c(name)))))) 
  (foldl
   (fn cnstr =>
    (fn (name,y,cnstr2) =>
     (App_c((prVis y),cnstr,(Ref_c(name))))))
   (Ref_c(mkNameGbl("f_"^x))) (nonarities S))
  (arities S)
   ;
*)

(* Instead, we rip off the reductions from the non-Relation types,
   (source in ind_relations.sml) and insert the odd judicious `n' *)

fun nlhs_of_reduction name_list schema_list (x,S) =
  App_c(ShowNorm,
(* the absence of the app_of_schema_applied removes the explicit
   parameter names no longer wanted since Conor hid them         *)  
	(recursor_applied_to_bindings name_list schema_list (x,S)),
	(iota_of_a(x,S)));

(* the hack of nphihash above does the same for the rhs *)
(* observe also the `binders' where there was a `nonarities' *)
fun nrhs_of_reduction name_list schema_list (x,S) =
  foldl 
  (fn cnstr =>
   (fn (name,y,schema) =>
    App_c((prVis y),cnstr,(nphihash schema   
			   (recursor_applied_to_bindings
			    name_list schema_list (name,schema))
			   (Ref_c(name)))))) 
  (foldl
   (fn cnstr =>
    (fn (name,y,cnstr2) =>
     (App_c((prVis y),cnstr,(Ref_c(name))))))
   (Ref_c(mkNameGbl("f_"^x))) (binders S))
  (arities S);

(* ie the above are almost the non-Rel reductions *)

fun nmake_reductions name_list schema_list typestr=
     Red_c((nall_bindings name_list schema_list typestr),
   (map (fn (x,S) => 
     ((nlhs_of_reduction name_list schema_list (x,S)),
      (nrhs_of_reduction name_list schema_list  (x,S))))
    schema_list));
    

fun do_weak_inductive_type (safe:bool) (with_bindings)
                      (declaration_bindings)
                      (schema_bindings)
                      (is_relation:bool) 
                      (typestr:cnstr_c) = 
  let
    val init_context = redo_bindings_with_dependency safe with_bindings
                                                     declaration_bindings
				                     schema_bindings
    val schema_list =
      nice_schemas (make_schema_list declaration_bindings schema_bindings)
    val disj_sch_list = make_disj_var_schemas schema_list
    val name_list = make_name_list declaration_bindings schema_bindings
    val _ = if (typestr <> Ref_c("TYPE") )
      then 
     message "Your value for ElimOver is ignored in defining a relation \n"
      else ()
  in
    ((init_context @ (neliminators name_list schema_list typestr)),
     (if is_relation then (Prop_c) 
      else (nmake_reductions name_list disj_sch_list typestr)))
 end;

(*

val schema = [("nil",Ref_s(Head("list"))),
("cons",
Bind_s((Pi,Hid,(UnFroz,Local),[],["a"],Ref_c("A")),
Bind_sc((Pi,Vis,(UnFroz,Local),[],["l"],Ref_s(Head("list"))),Ref_s(Head("list")))))];

val blah = ("Even",Bind_c((Pi,Vis,(UnFroz,Local),[],["n"],Ref_c("nat")),Prop_c));
    
val schema = [("ev0",Ref_s(Appl_a(ShowNorm,(Head("Even")),Ref_c("zero"))))];


val schema = [("ev0",Ref_s(Appl_a(ShowNorm,(Head("Even")),Ref_c("zero")))),
  ("ev1",
  Bind_s((Pi,Vis,(UnFroz,Global),[],["n"],Ref_c("nat")),
  Bind_sc((Pi,Vis,(UnFroz,Global),[],["x1"],
  Ref_s(Appl_a(ShowNorm,Head("Even"),Ref_c("n")))),
  Ref_s(Appl_a(ShowNorm,Head("Even"),
  (App_c(ShowNorm,Ref_c("suc"),App_c(ShowNorm,Ref_c("suc"),Ref_c("n")))))))))];
    

    
Simplest possible test data !!    

TYPE==Prop;
Inductive [nat:Prop] Constructors [zero:nat][suc:nat -> nat];
(* [Even:nat -> Prop];
[ev0:Even zero];
[ev1:{n:nat}(Even n) -> (Even (suc (suc n)))];
*)
Inductive [Even:nat -> Prop]
Constructors [ev0:Even zero]
[ev1:{n:nat}(Even n) -> (Even (suc (suc n)))] Relation;
NoReductions;


Inductive [Even:nat -> Prop]
Constructors [ev0:Even zero]
Relation;

[Even_elim : {C_Even:nat->TYPE}(C_Even zero)->({n:nat}(C_Even n)->C_Even (suc (suc n)))->{x1:nat}(Even x1)->C_Even x1];



[[C_even:nat->TYPE]
 [f_ev0 :C_even zero]
 [f_ev1 :{n:nat}{x1_ih:(C_even n)}C_even (suc (suc n))]
 [n:nat]
 [x1:Even n]
    Even_elim C_even f_ev0 f_ev1 zero ev0 ==> f_ev0
 || Even_elim C_even f_ev0 f_ev1 (suc (suc n)) (ev1 n x1) ==> 
         f_ev1 n (Even_elim C_even f_ev0 f_ev1 n x1)];

[[C_Even:nat->TYPE]
[f_ev0:C_Even zero]
[f_ev1:{n:nat}(C_Even n)->C_Even (suc (suc n))]
[n:nat]
[x1:Even n]
   Even_elim C_Even f_ev0 f_ev1 (suc (suc n)) (ev1 n x1)  ==>  
          f_ev1 n (Even_elim C_Even f_ev0 f_ev1 n x1)
|| Even_elim C_Even f_ev0 f_ev1 zero ev0  ==>  f_ev0]


Inductive [transclo:A -> A -> Prop] Parameters  [A:Type(0)]
[R:A -> A -> Prop]
Constructors [base:{a,b:A}(R a b) -> (transclo a b)]
[trans:{a,b,c:A}(transclo a b) -> (transclo b c) -> (transclo a c)]
Unsafe Relation ;


Goal not (Even one);
Intros H;
Refine Even_elim ([n:nat](Eq n one) -> absurd);
Refine +3 H;
Refine +2 Eq_refl;
Refine zero_not_one;
intros;
Refine zero_not_suc;
Refine +1 Eq_sym;
Refine +1 suc_injective;
Refine +1 H1;
Save not_Even_one;





*)
end end

(*</XMP>*)
