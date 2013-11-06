(* Record types in lego, done via inductive types *)

functor FunRecord (structure Concrete:CONCRETE
		   structure Inductive:INDUCTIVE
		   sharing type Concrete.cnstr_c=Inductive.cnstr_c)
    : RECORD =
    struct
	local
	    open Concrete open Inductive
	in
	    exception sch_err=sch_err
	    type cnstr_c=cnstr_c
		
fun make_into_single_constr ([]) name = Ref_c(name) 
| make_into_single_constr ((Lda,b,(UnFroz,Local),[],l,cn)::lis) name 
  =   Bind_c((Pi,Vis,(UnFroz,Global),[],l,cn), (make_into_single_constr lis name))
| make_into_single_constr _ name = raise sch_err "Invalid record type";
    

fun phizero_prime t1 (Ref_s(s)) = t1
  | phizero_prime t1 (Bind_s((Pi,x,_,_,l,c),c1)) =
                     Bind_c((Pi,x,(UnFroz,Local),[],[""],c),
                            (phizero_prime t1 c1))  
  | phizero_prime t1 _ = raise sch_err 
                       "Schema is not strictly positive";

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

fun subst_l l Prop_c           = Prop_c |
    subst_l l (Type_c(s))      = Type_c(s) |
    subst_l l (TypeAbs_c(x))   = TypeAbs_c(x) |
    subst_l (a,b) (Ref_c(x))   = if a=x then b else Ref_c(x) |
    subst_l l (App_c(x,c1,c2)) = 
              App_c(x,(subst_l l c1),(subst_l l c2)) |
    subst_l (a,b) (Bind_c((x,y,c,d,l1,c1),c2)) =
                  if (mem a l1) then Bind_c((x,y,c,d,l1,c1),c2)
      else Bind_c((x,y,c,d,l1,(subst_l (a,b) c1)),(subst_l (a,b) c2)) |
    subst_l l (Tuple_c(l1,c)) = Tuple_c(map (fn x => (subst_l l x)) l1,
					(subst_l l c))  |
    subst_l l (Proj_c(p,c))   = Proj_c(p,subst_l l c) |
    subst_l l (Cast_c(c1,c2)) = Cast_c((subst_l l c1),(subst_l l c2)) |
    subst_l l (Var_c(_)) = raise sch_err "Metavariables not allowed here" |
    subst_l l NewVar_c   = raise sch_err "Metavariables not allowed here" |
    subst_l l Bot_c      = Bot_c |
    subst_l l _          = raise sch_err "error in subst_l";

fun subst_list [] c name = c |
    subst_list (a::l) c name =
      subst_l (a,(App_c(ShowNorm,Ref_c(a),Ref_c(name^"_var"))))
      (subst_list l c name);

fun get_x_to_type name names_done ty =
    Bind_c((Lda,Vis,(UnFroz,Global),[],[name^"_var"],Ref_c(name)),
     (subst_list names_done ty name));


fun make_function S (string,_,var_ty) name names_done =
    ((Let,Def,(UnFroz,Global),[],[string],
    (App_c(ShowNorm,(App_c(ShowNorm,Ref_c(name^"_elim"), 
       (get_x_to_type name names_done var_ty))),
	   (make_identity_fun S (string,1,var_ty))))));
    

fun make_all_recs_aux name schema stuff [] = [] |
    make_all_recs_aux name schema stuff ((var_name,vsort,var_type)::l)
    =
   (make_function schema (var_name,vsort,var_type) name stuff) 
   :: (make_all_recs_aux name schema (var_name::stuff) l);
   
fun make_all_records name schema =
    let val list_of_binders = binders schema
in
    make_all_recs_aux name schema []
    list_of_binders
    end;

fun do_record_type (params) (decl_bindings) 
    (record_bindings) (typestr:cnstr_c) =
  let
    val name = hd (get_names decl_bindings)
    val schema_bindings = [(Lda,Vis,(UnFroz,Global),[],["make_"^name],
		  (make_into_single_constr record_bindings name))]
    val init_context = redo_bindings_with_dependency false params
                                                     decl_bindings
				                     schema_bindings
    val schema_list =
    nice_schemas (make_schema_list decl_bindings schema_bindings)
    val disj_sch_list = make_disj_var_schemas schema_list
    val name_list = make_name_list decl_bindings schema_bindings
    val (_,S) = hd schema_list
  in
    ((init_context @ (eliminators name_list schema_list typestr)),
     (make_reductions name_list disj_sch_list typestr),
     (make_all_records name S))
 end;

(*

"test"
val schema= Bind_s((Pi,Vis,(UnFroz,Global),[],["a"],Ref_c("A")),
Bind_s((Pi,Vis,(UnFroz,Global),[],["b"],App_c(ShowNorm,Ref_c("B"),Ref_c("a"))),
       Ref_s(Head("test"))));


((test_elim (B,test_var:test'(B a))) (B,a:A'(B,b:(B a)'b)))


((test_elim (B,test_var:test'(B (a test_var)))) (B,a:A'(B,b:(B a)'b)))

*)

end end
