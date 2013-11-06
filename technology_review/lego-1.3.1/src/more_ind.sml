(* For trying to do automatic disjointness of constructor proofs
   in lego *)

functor FunTheorems (structure Concrete:CONCRETE
		     structure Inductive:INDUCTIVE
		     sharing type Concrete.cnstr_c=Inductive.cnstr_c) :
     THEOREMS =
    struct
	local
	    open Concrete
	    open Inductive
	in
	    type cnstr_c=Concrete.cnstr_c
	    exception sch_err=sch_err

(* All of this assumes that we are defining only a datatype,
  i.e. occurences of Appl_a are forbidden in schemas *)


(* A principle component of this is a version of theta_zero
   where we abstract instead of pi-bind by underscore..
*)

val absurd = Ref_c("absurd");
    
val legotrue = App_c(ShowNorm,Ref_c("not"),Ref_c("absurd"));
    
val proof_of_legotrue = (App_c(NoShow,Ref_c("Id"),Ref_c("absurd")));
    
fun blank_to_prop name = Bind_c((Lda,Vis,(UnFroz,Global),[],[""],Ref_c(name)),Prop_c);
    

fun get_name schema = fst (get_name_and_type schema);
    


fun phizero_prime t1 (Ref_s(s)) = t1
  | phizero_prime t1 (Bind_s((Pi,x,_,_,l,c),c1)) =
                     Bind_c((Pi,x,(UnFroz,Local),[],[""],c),
                            (phizero_prime t1 c1))  
  | phizero_prime t1 _ = raise sch_err 
                       "Schema is not strictly positive";


fun all_pi_something S t t1 = (* S is a schema, t,t1 are constr_c *)
     let val l1 = binders S;
	 val (name,ty) = get_name_and_type S;
	 val l2 = arities S
     in
	 let val begin = foldr 
		  (fn (str,x,schema) => (fn so_far => Bind_c(
            (Lda,x,(UnFroz,Global),[],[""],(phizero_prime t1 schema)),
		  so_far)))
             t l2
        in 
	     foldr (fn (name,x,cnstr) => (fn so_far => 
	       Bind_c((Lda,x,(UnFroz,Global),[],[""],cnstr),so_far))) begin l1
        end 
  end;

fun bind_by_list ([]) init = init
  | bind_by_list ((a,x,y)::l) init = 
    bind_by_list l (Bind_c((Pi,x,(UnFroz,Local),[],[a],y),init));
    

fun equality_part_only (n,S1) (m,S2) =
  App_c(ShowNorm,App_c(ShowNorm,Ref_c("Eq"),
			    iota_of_a (n,S1)),iota_of_a (m,S2));
  
fun construct_theorem (n,S1) (m,S2) = 
  bind_by_list ((binders S1)@(binders S2))
  (App_c(ShowNorm,Ref_c("not"),(equality_part_only (n,S1) (m,S2))));
  
fun lambda_bind_by_list ([]) init = init
  | lambda_bind_by_list ((a,x,y)::l) init = 
    lambda_bind_by_list l (Bind_c((Lda,x,(UnFroz,Local),[],[a],y),init));
  
(* Supposed to construct the type of the theorem that
   the binders n and m are distinct... *)

(* This appears to do the right thing on a simple case now.... *)


(* Now a function to construct the proof term !! *)


fun make_up_jj datatype_name name_list list_of_schemas_and_names (n,S1) =
   foldl 
    (fn concrete   =>
    (fn (cons_name,schema) =>
    let val new_term = 
          if cons_name =n 
             then   (all_pi_something schema legotrue (Prop_c))
             else  (all_pi_something schema absurd (Prop_c))
    in (App_c(ShowNorm,concrete,new_term))
    end  ))
   (
foldl 
(fn so_far =>
   (fn (other_name,_) => 
App_c(ShowNorm,so_far,blank_to_prop other_name)))
(Ref_c(datatype_name^"_elim"))
name_list
) 
list_of_schemas_and_names;


fun whole_proof_term datatype_name name_list list_of_schemas_and_names (n,S1) (m,S2)
= 
lambda_bind_by_list ((binders S1)@(binders S2))
(Bind_c((Lda,Vis,(UnFroz,Global),[],["H"],(equality_part_only (n,S1) (m,S2))),
  App_c(ShowNorm,
   (App_c(ShowNorm,
    (App_c(ShowNorm,Ref_c("Eq_subst"),Ref_c("H"))),
    (make_up_jj datatype_name name_list list_of_schemas_and_names (n,S1)))),
	(App_c(NoShow,Ref_c("Id"),Ref_c("absurd"))))));



fun make_cast datatype_name name_list list_of_schemas_and_names (n,S1) (m,S2) =
  Cast_c(
    (whole_proof_term datatype_name name_list 
          list_of_schemas_and_names (n,S1) (m,S2)),
	 (construct_theorem (n,S1) (m,S2)));

fun make_all_disjointness_theorems name_list schemas [] =
     []
|   make_all_disjointness_theorems name_list schemas 
             ((name,schema)::rest_of_list) =
    let val datatype_name = get_name schema in
    foldr 
    (fn (new_name,new_schema) =>
        (fn theorems_so_far =>
            if ((get_name new_schema)=datatype_name) 
               then (name,new_name,(make_cast datatype_name name_list schemas
                     (name,schema) (new_name,new_schema)))::theorems_so_far
               else theorems_so_far))
    (make_all_disjointness_theorems name_list schemas rest_of_list)
    rest_of_list
    end;
    


(* To actually give these theorems.... *)

(* Now work on constructor injectivity *)

fun make_identity_fun S (string,_,var_ty)  = 
     (* S is a schema, string is a binder name in S  *)
     let val l1 = binders S;
	 val (name,ty) = get_name_and_type S;
	 val l2 = arities S
     in
	 let val begin = foldr 
		  (fn (str,x,schema) => (fn so_far => Bind_c(
            (Lda,x,(UnFroz,Global),[],[""],(phizero_prime var_ty schema)),
		  so_far)))
             (Ref_c(string)) l2
        in 
	     foldr (fn (name,x,cnstr) => (fn so_far => 
	       Bind_c((Lda,x,(UnFroz,Global),[],[name],cnstr),so_far))) begin l1
        end 
  end;

fun blank_to_type name ty =
      Bind_c((Lda,Vis,(UnFroz,Global),[],[""],Ref_c(name)),ty);

fun make_up_kk datatype_name name_list list_of_schemas_and_names 
    (n,S1) (var_name,_,var_type) =
   foldl 
    (fn concrete   =>
    (fn (cons_name,schema) =>
    let val new_term = 
          if cons_name =n 
             then   (make_identity_fun schema (var_name,1,var_type))
             else  (all_pi_something schema (Ref_c(var_name^"1")) var_type)
    in (App_c(ShowNorm,concrete,new_term))
    end  ))
   (
foldl 
(fn so_far =>
   (fn (other_name,_) => 
App_c(ShowNorm,so_far,blank_to_type other_name var_type)))
(Ref_c(datatype_name^"_elim"))
name_list
    )
list_of_schemas_and_names;

fun bind_by_list_funny name ([]) init = init
  | bind_by_list_funny name ((a,x,y)::l) init = 
    (* if a=name then  *)
    bind_by_list_funny name l (Bind_c((Pi,x,(UnFroz,Local),[],[a^"1",a^"2"],y),init))
    (* else bind_by_list_funny name l (Bind_c((Pi,x,(UnFroz,Local),[],[a],y),init))  *);

(* changed to make theorem correct *)
(* This won't work if there are dependencies in the schema parameters...
   I don't even know if you *can* prove the injectiveness...nor
   does Thorsten !! *)
(*
fun new_iota_of_a string1 string2  (x,S) = 
   foldl
   (fn cnstr => (fn (name,x,cnstr2) =>
    if name=string1 then (App_c((prVis x),cnstr,Ref_c(string2)))
       else (App_c((prVis x),cnstr,Ref_c(name)))
                )
   )
   (Ref_c(x)) 
   (binders S);   


fun equality_part_only_2 (n,S) var_name  =
  App_c(ShowNorm,App_c(ShowNorm,Ref_c("Eq"),
     (new_iota_of_a var_name (var_name^"1") (n,S))),
     (new_iota_of_a var_name (var_name^"2") (n,S)));

New versions of these functions follow.
*)


fun new_iota_of_a string1 (x,S) =
    foldl
    (fn cnstr => (fn (name,x,cnstr2) =>
     (App_c((prVis x),cnstr,Ref_c(name^string1)))
        ))
    (Ref_c(x)) 
    (binders S);
 
 fun equality_part_only_2 (n,S) var_name  =
   App_c(ShowNorm,App_c(ShowNorm,Ref_c("Eq"),
      (new_iota_of_a "1" (n,S))),
      (new_iota_of_a "2" (n,S)));

fun construct_theorem_2 (n,S) (var_name,_,_) =
  bind_by_list_funny  var_name (binders S) 
(Bind_c((Pi,Vis,(UnFroz,Local),[],[""],(equality_part_only_2 (n,S) var_name)),
 App_c(ShowNorm,App_c(ShowNorm,Ref_c("Eq"),
		      Ref_c(var_name^"1")),Ref_c(var_name^"2"))));

    
fun lambda_bind_by_list_funny name ([]) init = init
  | lambda_bind_by_list_funny name ((a,x,y)::l) init = 
    (* if a=name then  *)
    lambda_bind_by_list_funny name l (Bind_c((Lda,x,(UnFroz,Local),[],[a^"1",a^"2"],y),init))
    (*  else lambda_bind_by_list_funny name l 
       (Bind_c((Lda,x,(UnFroz,Local),[],[a],y),init))    *);
  (* Changed to make theorem correct *)

fun func_type datatype_name var_type =
    Bind_c((Pi,Vis,(UnFroz,Local),[],[""],Ref_c(datatype_name)),var_type);
    
fun whole_proof_term_2 datatype_name name_list 
  list_of_schemas_and_names (n,S1) (var_name,x,var_type) =
lambda_bind_by_list_funny var_name (binders S1)
(Bind_c((Lda,Vis,(UnFroz,Global),[],["H"],(equality_part_only_2 (n,S1) var_name)),
   (App_c(ShowNorm,
    (App_c(ShowNorm,Ref_c("Eq_resp"),
(Cast_c((make_up_kk datatype_name name_list list_of_schemas_and_names (n,S1)
	   (var_name,x,var_type)),(func_type datatype_name var_type))))),
Ref_c("H")))));


fun make_cast_2 
datatype_name name_list list_of_schemas_and_names (n,S1) 
(var_name,_,var_type) =
  Cast_c(
    (whole_proof_term_2 datatype_name name_list 
          list_of_schemas_and_names (n,S1) (var_name,1,var_type)),
	 (construct_theorem_2 (n,S1) (var_name,1,var_type)));

(* Copied from below *)
fun make_all_inj_theorems name_list schemas [] =
     []
|   make_all_inj_theorems name_list schemas 
             ((name,schema)::rest_of_list) =
    let val datatype_name = get_name schema 
        val list_of_binders = binders schema
in
    foldr 
    (fn (var_name,vsort,var_type) =>
        (fn theorems_so_far =>
               (name,var_name,(make_cast_2 datatype_name name_list schemas
                  (name,schema) (var_name,vsort,var_type)))::theorems_so_far))
    (make_all_inj_theorems name_list schemas rest_of_list)
    list_of_binders
    end;
    
(* To actually give these theorems.... *)

(* Now think about theorem that every term is constructed from
   the constructors *)


(* First part we need to construct is a schema, for each binder,
   an existential quantification ... *)

fun make_exists str typ const =
  App_c(ShowNorm,Ref_c("Ex"),
	Bind_c((Lda,Vis,(UnFroz,Local),[],[str],typ),const));
  

fun do_existentials S constructor =
    foldr 
    (fn (str,_,cons) =>
        (fn typ =>
            make_exists (str^"_ex") cons typ))
    constructor
    (binders S);
    
fun another_iota_of_a (x,S) = 
   foldl
   (fn cnstr => (fn (name,x,cnstr2) =>
     (App_c((prVis x),cnstr,Ref_c(name^"_ex")))
                )
   )
   (Ref_c(x)) 
   (binders S);


fun appropriate_equality (x,S) sch_new =
    App_c(ShowNorm,
         (App_c(ShowNorm,Ref_c("Eq"),sch_new)),
	 (another_iota_of_a (x,S)));
    
fun part_of_theorem (x,S) new_sch =
    do_existentials S (appropriate_equality (x,S) new_sch);

fun or_these_together constr1 constr2 =
    App_c(ShowNorm,App_c(ShowNorm,Ref_c("or"),constr1),constr2);
    
fun pick_out_right_schemas list_of_schema dtname
    = filter_pos (fn (n,S) => (dtname=get_name S)) list_of_schema;
    
fun all_ors_on_theorem [(n,S)] new_name dtname =
        (part_of_theorem (n,S) (Ref_c(new_name)))
|   all_ors_on_theorem ((n,S)::list_of_schema) new_name dtname =
    (or_these_together (part_of_theorem (n,S) (Ref_c(new_name)))
       (all_ors_on_theorem list_of_schema new_name dtname))
|   all_ors_on_theorem _ new_name dtname =
    raise Bug 
	("No appropriate schemas found for datatype "^dtname);
	
fun real_theorem list_of_schema datatype_name =
  Bind_c((Pi,Vis,(UnFroz,Local),[],[(datatype_name^"_var")],Ref_c(datatype_name)),
   (all_ors_on_theorem 
      (pick_out_right_schemas list_of_schema datatype_name)
      (datatype_name^"_var") datatype_name)
   );
  

(* Theorem is checked now ... *)

(* Now for proof.... *)


fun elim_rule_applied_to_prop list_of_schema datatype_name   
   datatype_list  =
   foldl
   (fn so_far =>
       (fn (name,_) =>
   if (name=datatype_name)
   then App_c(ShowNorm,so_far,
          Bind_c((Lda,Vis,(UnFroz,Local),[],[(datatype_name^"_var")],
		  Ref_c(datatype_name)),
   (all_ors_on_theorem 
        (pick_out_right_schemas list_of_schema datatype_name)
        (datatype_name^"_var") datatype_name)
     ))
   else 
         App_c(ShowNorm,so_far,
         Bind_c((Lda,Vis,(UnFroz,Local),[],[""],
		  Ref_c(name)),legotrue
     ))
   ))
   (Ref_c(datatype_name^"_elim"))
   datatype_list;

(* very much like the theorem *)


fun mem_left x [] = false
  |   mem_left x ((a,b)::l) = (a = x) orelse mem_left x l;
      
fun more_new_iota_of_a lofvar (x,S) = 
   foldl
   (fn cnstr => (fn (name,x,cnstr2) =>
    if (mem_left name lofvar) then (App_c((prVis x),cnstr,Ref_c(name^"1")))
       else (App_c((prVis x),cnstr,Ref_c(name)))
                )
   )
   (Ref_c(x)) 
   (binders S);

fun make_eq_refl_term (x,S) =
    App_c(ShowNorm,Ref_c("Eq_refl"),(iota_of_a (x,S)));
    

fun make_equality_term (x,S) changed_vars =
    App_c(ShowNorm,
         (App_c(ShowNorm,Ref_c("Eq"),iota_of_a (x,S))),
	 (more_new_iota_of_a changed_vars (x,S)));

(* changed vars is the list of variables whose names are to be
   changed to the primed form *)
(*
fun make_exists_intro str typ const =
  App_c(ShowNorm,exintros_of_old_type,
	Bind_c((Lda,Vis,(UnFroz,Local),[],[str],typ),const));
*)


fun make_exists_intro str typ const =
  App_c(ShowNorm,(App_c(ShowNorm,Ref_c("ExIntro"),NewVar_c)),
	Bind_c((Lda,Vis,(UnFroz,Local),[],[str],typ),const));



fun do_next_intros (x,S) new_var new_type changed_vars_list =
    make_exists_intro (new_var^"1") new_type
  (foldr 
   (fn  (a,ty)  =>
     (fn (constrc:cnstr_c)  =>
        (make_exists (a^"1") ty constrc)))
  (make_equality_term (x,S) ((new_var,new_type)::changed_vars_list))
   changed_vars_list
  );
  
fun do_all_intros (x,S) init =
    foldr
    (fn (str,_,typ) =>
        (fn (so_far,l)   =>
          (App_c(ShowNorm,(do_next_intros (x,S) str typ l),so_far)
         ,((str,typ)::l))
        )
    )
   (init,[])
   (binders S);
    
fun all_ex_intros (x,S) =
    let val (out,_) = do_all_intros (x,S) (make_eq_refl_term (x,S))
    in out end;
	
fun apply_inr cn (n,S) (n1,S1) =
    App_c(ShowNorm,
          App_c(NoShow,Ref_c("inr"),
                (part_of_theorem (n,S) (iota_of_a (n1,S1))))
          ,cn);

fun pick_out_right_schemas_funny list_of_schema dtname
   = filter_pos (fn ((n,S),_) => (dtname=get_name S)) list_of_schema;
   
fun new_all_ors_on dname [((n,S),_)] new_cn  =
        (part_of_theorem (n,S) (new_cn))
|   new_all_ors_on dname (((n,S),_)::list_of_schema) new_cn =
    (or_these_together (part_of_theorem (n,S) (new_cn))
       (new_all_ors_on dname list_of_schema new_cn))
|   new_all_ors_on dname _ new_cn =
    raise Bug 
	("No appropriate schemas found for datatype"^dname);

fun apply_inl dname cn (n,S) funny_list =
    App_c(ShowNorm,
          App_c(NoShow,(App_c(NoShow,Ref_c("inl"),NewVar_c)),
                (new_all_ors_on dname 
      (pick_out_right_schemas_funny funny_list dname) (iota_of_a (n,S))))
          ,cn); 

fun map_inr_to_appro dname (n,S) list_of_stuff =
    map (fn ((n1,S1),x) => 
     if (dname = get_name S1) then 
        ((n1,S1),apply_inr x (n,S) (n1,S1))
        else ((n1,S1),x))
	    (list_of_stuff);
	    
fun do_apply count dname stuff_so_far (n,S) =
    if (count=0) then 
        ((((n,S),(all_ex_intros (n,S)))::stuff_so_far),1)
           else 
       ((((n,S),(apply_inl dname 
		 (all_ex_intros (n,S)) (n,S) stuff_so_far))::
	 (map_inr_to_appro dname (n,S) stuff_so_far)),count);
       

fun all_ins_on_theorem dtname schema_list =
   foldr   
   (fn (x,S) =>
   (fn (so_far,n) =>
      if (dtname=get_name S)
         then
           (do_apply n dtname so_far (x,S))
         else ((((x,S),proof_of_legotrue)::so_far),n)))
   ([],0)
   schema_list;
   

fun outer_abstractions1 (n,S) list_of_schema name cn1 =
   let val sch_list = arities S     
   in 
      foldr
      (fn (str,v,sch)  =>
          (fn so_far =>
            Bind_c((Lda,v,(UnFroz,Global),[],[""],
            (if (name=get_name sch) then
             (bind_by_list (binders sch)
	     (all_ors_on_theorem 
               (pick_out_right_schemas list_of_schema name)
	       str name)
            )
            else (legotrue)
            )),so_far)))
      cn1
      sch_list
   end;
   
fun outer_abstractions2 (n,S) list_of_schema name cn1 =
    lambda_bind_by_list (rev (binders S))
    (outer_abstractions1 (n,S) list_of_schema name cn1);

fun abstract_on_ins list_of_schema name  =
    map
    (fn ((n,S),cn1) => 
     outer_abstractions2 (n,S) list_of_schema name cn1) 
    (fst (all_ins_on_theorem name list_of_schema));
     
fun whole_ex_theorem list_of_schema datatype_name dtype_list =
    foldl
    (fn so_far =>
        fn  cn =>
           App_c(ShowNorm,so_far,cn))
    (elim_rule_applied_to_prop list_of_schema datatype_name dtype_list)
    (abstract_on_ins list_of_schema datatype_name);
    
(* Now think about the or's.... *)
(* The first schema is always inl with sucessive schemas
   an extra  inr ?... *)

fun make_ex_cast list_of_schema datatype_name dtype_list =
  Cast_c((whole_ex_theorem list_of_schema datatype_name dtype_list),
         (real_theorem list_of_schema datatype_name));
  
fun list_all_ex_theorem list_of_schema dtype_list = 
   (map
   (fn (name,_) => 
    (Let,Def,(UnFroz,Global),[],[name^"_char"],
	    (make_ex_cast list_of_schema name dtype_list)))
   dtype_list);

fun list_all_dis_theorems name_list schema_list =
    let val list_of_thms =  make_all_disjointness_theorems name_list
	                   schema_list schema_list
    in
    (map
       (fn (name1,name2,cast) => 
          (Let,Def,(UnFroz,Global),[],[name1^"_not_Eq_"^name2],cast))
     list_of_thms)
    end;

fun list_inj_theorems name_list schema_list =
    let val list_of_thms =  make_all_inj_theorems name_list
	                   schema_list schema_list
    in
     (map    
       (fn (name1,name2,cast) => 
          (Let,Def,(UnFroz,Global),[],[name1^"_is_inj_"^name2],cast))
      list_of_thms)
    end;

fun list_all_theorems sch_list dtype_list =
    ((list_all_dis_theorems dtype_list sch_list)@
    (list_inj_theorems dtype_list sch_list)@
   (list_all_ex_theorem  sch_list dtype_list));

fun do_inductive_type_with_theorems (safe:bool) (with_bindings)
                      (declaration_bindings)
                      (schema_bindings) (is_relation:bool) 
                       (typestr:cnstr_c)
                       = 
  let
    val init_context = redo_bindings_with_dependency safe with_bindings
                                                     declaration_bindings
				                     schema_bindings
    val schema_list =
      nice_schemas (make_schema_list declaration_bindings schema_bindings)
    val disj_sch_list = make_disj_var_schemas schema_list
    val name_list = make_name_list declaration_bindings schema_bindings
  in
    ((init_context @ (eliminators name_list schema_list typestr)),
  (make_reductions name_list disj_sch_list),
   (list_all_theorems disj_sch_list name_list)
    )
end;

fun do_just_theorems (with_bindings)
                      (declaration_bindings)
                      (schema_bindings) 
                       = 
  let
    val schema_list =
      nice_schemas (make_schema_list declaration_bindings schema_bindings)
    val disj_sch_list = make_disj_var_schemas schema_list
    val name_list = make_name_list declaration_bindings schema_bindings
  in
    (list_all_theorems disj_sch_list name_list)
end;


(*

fEval x
val (a,b) = it; legoprint a; legoprint b;
*)    
(*

val sche = Bind_s((Pi,Vis,(UnFroz,Local),[],["a"],Ref_c("A")),
    Bind_s((Pi,Vis,(UnFroz,Local),[],["x"],Ref_c("a")),Ref_s(Head("list"))));

val sche =Bind_s((Pi,Hid,(UnFroz,Local),[],["a"],Ref_c("A")),
    Bind_sc((Pi,Vis,(UnFroz,Local),[],["l"],Ref_s(Head("list"))),Ref_s(Head("list"))));
    
val sche2 = Ref_s(Head("list"));
 

val list = [("list",Type_c)]
val schema = [("nil",Ref_s(Head("list"))),
("cons",
Bind_s((Pi,Hid,(UnFroz,Local),[],["a"],Ref_c("A")),
Bind_sc((Pi,Vis,(UnFroz,Local),[],["l"],Ref_s(Head("list"))),Ref_s(Head("list")))))];

Inductive [list:Type] Parameters [A:Type]
Constructors [nil:list][cons:{a|A}{l:list}list];

Inductive [nat:Type] Constructors [zero:nat][zero2:nat]
[succ:{x:nat}nat];

val nat = [("nat",Type_c)]
val schema = [("zero",Ref_s(Head("nat"))),("zero2",Ref_s(Head("nat"))),
    ("succ",Bind_sc((Pi,Vis,(UnFroz,Local),[],["x"],Ref_s(Head("nat"))),Ref_s(Head("nat"))))]


Inductive [red,white:Type] Constructors
[zero_r:red][succ_r:{r:red}white][succ_w:{w:white}red];

val candy = [("red",Type_c),("white",Type_c)];
val c_schema = [("zero_r",Ref_s(Head("red"))),
("succ_r",Bind_sc((Pi,Vis,(UnFroz,Local),[],["r"],Ref_s(Head("red"))),Ref_s(Head("white")))),
("succ_w",Bind_sc((Pi,Vis,(UnFroz,Local),[],["w"],Ref_s(Head("white"))),Ref_s(Head("red"))))];


*)

(* Nothing yet for parameterised/relations stuff *)

(* Found bug---seems we need to give even more implicit args to
   inl and inr !!
First part... fixed now

PLUS_elim ([PLUS_var:PLUS]or (Ex|A ([x2_ex:A]Eq|PLUS PLUS_var (LEFT x2_ex))) (Ex|B ([x1_ex:B]Eq|PLUS PLUS_var (RIGHT x1_ex))))


Need the following...

PLUS_elim ([PLUS_var:PLUS]or (Ex|A ([x2_ex:A]Eq|PLUS PLUS_var (LEFT x2_ex))) (Ex|B ([x1_ex:B]Eq|PLUS PLUS_var (RIGHT x1_ex)))) 
([x2:A]inl|?|(Ex|B ([x1_ex:B]Eq|PLUS (LEFT x2) (RIGHT x1_ex))) (ExIntro ([x2_ex:A]Eq|PLUS (LEFT x2) (LEFT x2_ex)) (Eq_refl (LEFT x2)))) 
([x1:B]inr|(Ex|A ([x21:A]Eq|PLUS (RIGHT x1) (LEFT x21)))|? (ExIntro ([x1_ex:B]Eq|PLUS (RIGHT x1) (RIGHT x1_ex)) (Eq_refl (RIGHT x1))))

instead of what we got...
[x2:A]inl|(Ex|A ([x21:A]Eq|PLUS (LEFT x2) (LEFT x21)))(ExIntro|A ([x21:A]Eq|PLUS (LEFT x2) (LEFT x21))|x2 (Eq_refl|PLUS (LEFT x2)))

*)

(* Found second bug ... on datatype for CCS with many
   constructors, problem is with two arities (I think) *)
(*
CCS_elim ([CCS_var:CCS]Ex|CCS ([x1_ex:CCS]Ex|CCS ([x2_ex:CCS]Eq|CCS CCS_var (SUM x1_ex x2_ex))))
with domain type  
{x1,x2:CCS}(Ex|CCS ([x1_ex:CCS]Ex|CCS ([x2_ex:CCS]Eq|CCS x1 (SUM x1_ex x2_ex))))->
(Ex|CCS ([x1_ex:CCS]Ex|CCS ([x2_ex:CCS]Eq|CCS x2 (SUM x1_ex x2_ex))))->
Ex|CCS ([x1_ex:CCS]Ex|CCS ([x2_ex:CCS]Eq|CCS (SUM x1 x2) (SUM x1_ex x2_ex)))

[x1,x2:CCS]
[_:Ex|CCS ([x1_ex:CCS]Ex|CCS ([x2_ex:CCS]Eq|CCS x1 (SUM x1_ex x2_ex)))]
[_:Ex|CCS ([x1_ex:CCS]Ex|CCS ([x2_ex:CCS]Eq|CCS x2 (SUM x1_ex x2_ex)))]
ExIntro|CCS ([x11:CCS]Ex|CCS ([x21:CCS]Eq|CCS (SUM x1 x2) (SUM x11 x21)))|x1 (ExIntro|CCS ([x21:CCS]Eq|CCS (SUM x1 x2) (SUM x1 x21))|x2 (Eq_refl|CCS (SUM x1 x2))) : 

{x1,x2:CCS}(Ex|CCS ([x1_ex:CCS]Ex|CCS ([x2_ex:CCS]Eq|CCS x2 (SUM x1_ex x2_ex))))->
(Ex|CCS ([x1_ex:CCS]Ex|CCS ([x2_ex:CCS]Eq|CCS x1 (SUM x1_ex x2_ex))))->
Ex|CCS ([x11:CCS]Ex|CCS ([x21:CCS]Eq|CCS (SUM x1 x2) (SUM x11 x21)))


*)

end end
