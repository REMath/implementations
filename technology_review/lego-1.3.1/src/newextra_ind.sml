(* Not right yet for mutual recursion..... need
   to get this right !!!! *)

functor FunDouble (structure Concrete:CONCRETE
		   structure Inductive:INDUCTIVE
		   sharing type Concrete.cnstr_c=Inductive.cnstr_c) : DOUBLE =
    struct
	local
	    open Concrete
	    open Inductive
	in
	    type cnstr_c=cnstr_c

fun mapply l c =
    foldl (fn so_far =>
    (fn (name,vsrt,_) => (App_c((prVis vsrt),so_far,Ref_c(name)))))
    c
    l;
    
fun mapply_var l c =
    foldl (fn so_far =>
    (fn (name,vsrt,_) => (App_c((prVis vsrt),so_far,Ref_c(name^"_f")))))
    c
    l;

fun new_binders_ind (Bind_c((_,d,_,_,l,s1),s)) = 
      (map (fn x => (x,d,s1)) l)@(new_binders_ind s)
  | new_binders_ind (_) = [];

					      
fun iota_prime_of_a (x,S) = 
   foldl
  (fn cnstr => (fn (name,x,cnstr2) =>
   (App_c((prVis x),cnstr,Ref_c(name^"'")))))
   (Ref_c(x)) (binders S);

fun start_up_special S z T_applied = 
     App_c(ShowNorm,T_applied,(iota_prime_of_a (z,S)));

fun dashify l = map (fn x => x^"'") l;
fun dashify_binds l = map (fn (x,y,z) => (x^"'",y,z)) l;    

fun is_dash str =
    last (explode str) = "'";
    
    
fun dashify_inside_binds str (Bind_c((x,y,c,d,l1,c1),c2))
      = if (is_dash (hd l1)) then
       (Bind_c((x,y,c,d,l1,(subst_c (str,str^"'") c1)),
         (dashify_inside_binds str c2))) 
       else (Bind_c((x,y,c,d,l1,c1),c2)) |
      dashify_inside_binds str constr = constr;

fun dashify_inside_list l c1 =
    fold (fn (str,rest) =>   dashify_inside_binds str rest)
    l c1;
    
fun dashify_subst l c1 =
    fold (fn ((str,_,_),rest) => subst_c (str,str^"'") rest) l c1;

fun phizero_T T_app (Ref_s(s)) z l1 = App_c(ShowNorm,T_app,z)
  | phizero_T T_app  (Bind_s((Pi,x,_,_,l,c),c1)) z l1=
                     Bind_c((Pi,x,(UnFroz,Local),[],(dashify l),
      (dashify_subst l1 c)   ),
  (dashify_inside_list l (phizero_T T_app  c1 (gen_app z x (dashify l)) l1)))
  | phizero_T _ _ z _ = raise sch_err "Schema is not strictly positive";

fun theta_end S z S1 z1 =
  let 
    val l1 = binders S1
    val (name,ty) = get_name_and_type S1
    val l2 = arities S1
    val T_app = App_c(ShowNorm,Ref_c("T_"^name),(iota_of_a (z,S)))
  in
    let val begin = foldr 
      (fn (str,x,schema) =>
       (fn so_far => Bind_c((Pi,x,(UnFroz,Local),[],[str^"_ih"],
			     (phizero_T T_app schema (Ref_c(str^"'")) l1)),
			    so_far)))
      (start_up_special S1 z1 T_app)
      l2
    in 
      foldr (fn (name,x,cnstr) =>
	     (fn so_far => Bind_c((Pi,x,(UnFroz,Local),[],[name^"'"],cnstr),
    (dashify_inside_binds name so_far))))
      begin
      l1
    end 
  end;

fun phizero_ext T_qunt (Ref_s(s)) z = T_qunt z
  | phizero_ext T_qunt  (Bind_s((Pi,x,_,_,l,c),c1)) z =
                     Bind_c((Pi,x,(UnFroz,Local),[],l,c),
                 (phizero_ext T_qunt  c1 (gen_app z x l)))
  | phizero_ext _ _ z = raise sch_err "Schema is not strictly positive";

(* This is wrong !!!! *)

fun theta_rest dname dtype S z S1 z1 =
  let 
    val l1 = binders S;
    val l2 = arities S;
    val lnames = new_binders_ind dtype   
    fun T_qunt x =  
      fold  (fn ((a,_,b),x) => Bind_c((Pi,Hid,(UnFroz,Local),[],[a],b),x))
      lnames
(*** Need to pi-bind also by binders in schema head ***)
     (Bind_c((Pi,Vis,(UnFroz,Local),[],["z"],(mapply lnames (Ref_c(dname)))),
             App_c(ShowNorm,App_c(ShowNorm,Ref_c("T_"^dname),x),Ref_c("z"))))
  in
    let val begin = foldr 
      (fn (str,x,schema) =>
       (fn so_far => Bind_c((Pi,x,(UnFroz,Local),[],[str^"_ih"],
			     (phizero_ext T_qunt schema (Ref_c(str)))),
			    so_far)))
      (theta_end S z S1 z1)
      l2
    in 
      foldr (fn (name,x,cnstr) =>
	     (fn so_far => Bind_c((Pi,x,(UnFroz,Local),[],[name],cnstr),so_far)))
      begin
      l1
    end 
  end;

fun make_theta_abstr dname dtype  S z S1 z1 =
  (Lda,Vis,(UnFroz,Local),[],[z^"_"^z1^"_case"],
        (theta_rest dname dtype S z S1 z1))(*:binder_c;*)


fun make_all_theta dname dtype schemalist start =
         foldr
         (fn (str,schem) => (fn rest =>
           (foldr 
             (fn (newstr,newschem) => (fn newrest =>
             Bind_c(make_theta_abstr dname dtype  schem str newschem newstr,newrest)))
            rest
            schemalist
         ) ))
         start
         schemalist;
	 

(* Here we need to  also pi bind by implict args to schema head *)
fun do_elim_rule name type_of_name =
   let val l1 = dashify_binds (new_binders_ind type_of_name)
            in
   App_c(ShowNorm,Ref_c(name^"_elim"),
   (fold  (fn ((a,_,b),x) => Bind_c((Lda,Hid,(UnFroz,Local),[],[a],b),x))
      l1
    (Bind_c((Lda,Vis,(UnFroz,Local),[],["z"],(mapply l1 (Ref_c(name)))),
    (fold  (fn ((a,_,b),x) => Bind_c((Pi,Hid,(UnFroz,Local),[],[a],b),x))
      l1
      (Bind_c((Pi,Vis,(UnFroz,Local),[],["z'"],(mapply l1 (Ref_c(name)))),
         App_c(ShowNorm,App_c(ShowNorm,Ref_c("T_"^name),Ref_c("z")),Ref_c("z'"))
	     )))))))   end;

fun do_inside_elim_head name nametype S z =  
   let val l1 = new_binders_ind nametype in
 App_c(ShowNorm,Ref_c(name^"_elim"),
  (fold  (fn ((a,_,b),x) => Bind_c((Lda,Hid,(UnFroz,Local),[],[a],(dashify_subst l1 b)),x))
      (dashify_binds l1)
(Bind_c((Lda,Vis,(UnFroz,Local),[],["z"],(mapply (dashify_binds l1) (Ref_c(name)))),
 (App_c(ShowNorm,(App_c(ShowNorm,Ref_c("T_"^name),iota_of_a (z,S))),Ref_c("z"))
))))) end ;
 

fun applied_theta z z1 arities binders =
    mapply_var arities (mapply binders (Ref_c(z^"_"^z1^"_case")));
    
fun phi_zero_inside_part (Ref_s(s)) z = z
  | phi_zero_inside_part (Bind_s((Pi,x,_,_,l,c),c1)) z =
                 (phi_zero_inside_part c1 (gen_app z x l))
  | phi_zero_inside_part _ z = raise sch_err "Schema is not strictly positive";

fun phi_zero_outside (Ref_s(s)) start = start 
  | phi_zero_outside  (Bind_s((Pi,x,_,_,l,c),c1)) z =
                     Bind_c((Pi,x,(UnFroz,Local),[],l,c),
                 (phi_zero_outside  c1 z))
  | phi_zero_outside  _ z = raise sch_err "Schema is not strictly positive";

(* Again need to pi-bind by binders of dname *)
fun approp_T str schem dname dtype =
     let val lname = new_binders_ind dtype in 
     phi_zero_outside schem
        (fold  (fn ((a,_,b),x) => Bind_c((Pi,Hid,(UnFroz,Local),[],[a],b),x))
        lname
      (Bind_c((Pi,Vis,(UnFroz,Local),[],["z"],(mapply lname (Ref_c(dname)))),
	     App_c(ShowNorm,(App_c(ShowNorm,Ref_c("T_"^dname),
      (phi_zero_inside_part schem  (Ref_c(str))))),
		   Ref_c("z"))))) end;

(* Must change the above function to also do a phizero
   like-trick....first change ''str'' to be a schema. *)

fun make_whole_second_elim dname nametype S z schema_list =
    let val l1 = binders S;
	val l2 = arities S;
        val start = 
            foldl (fn cnstr =>
                  (fn (name,schma) => 
                  App_c(ShowNorm,cnstr,(applied_theta z name l2 l1))))
            (do_inside_elim_head dname nametype S z)
            schema_list
    in
   foldr  (fn (name1,vsrt,typ) =>
           (fn cnstr =>
            Bind_c((Lda,vsrt,(UnFroz,Local),[],[name1],typ),cnstr)
           )
         ) 
  (foldr (fn (name,vsrt,schme) =>
           (fn cnstr =>
            Bind_c((Lda,vsrt,(UnFroz,Local),[],[name^"_f"],(approp_T name schme dname nametype)),cnstr)
           )
         )
   start
   l2)
   l1
    end;
    
fun make_all_elims schema_list dname d_type = 
    foldl
    (fn cnstr =>
        (fn (z,S) =>
    App_c(ShowNorm,cnstr,(make_whole_second_elim dname d_type S z schema_list)
    )))
    (do_elim_rule dname d_type)
    schema_list;

(*
fun double_T_of_C l str typestr = 
  fold  (fn ((a,b,_),x) => Bind_c((Pi,Hid,(UnFroz,Local),[],[a],b),x))
   (l @ (dashify_binds l)) 
   (Bind_c((Pi,Vis,(UnFroz,Local),[],[""],(start_T_of_C (dashify_binds l) str)),
  (Bind_c((Pi,Vis,(UnFroz,Local),[],[""],(start_T_of_C l str)),typestr))));
 
*)

fun double_T_of_C l str typestr = 
  fold  (fn ((a,b,_),x) => Bind_c((Pi,Hid,(UnFroz,Local),[],[a],b),x))
   l  
 (Bind_c((Pi,Vis,(UnFroz,Local),[],[""],(start_T_of_C l str)),
 (fold (fn ((a,b,_),x) => Bind_c((Pi,Hid,(UnFroz,Local),[],[a],b),x))
  (dashify_binds l)
(Bind_c((Pi,Vis,(UnFroz,Local),[],[""],(start_T_of_C (dashify_binds l) str))
 ,typestr)))))  ;

(*
The above new version of this function which will correct strange order of
arguments in double elim rule!
*)


fun do_all schemalist dname d_type all_dnames typestr  =
    foldr (fn (str,cnstr) =>
	     (fn rest => Bind_c((Lda,Vis,(UnFroz,Local),[],["T_"^dname],
				 (double_T_of_C (binders_ind cnstr) str typestr)),
				rest)))
    (make_all_theta dname d_type schemalist (make_all_elims schemalist dname d_type))
    all_dnames
;
        
fun add_it schemalist [(dname,d_type)] typestr =  
    [(Let,Def,(UnFroz,Global),[],[dname^"_double_elim"],
        (do_all schemalist dname d_type [(dname,d_type)] typestr ))] |
    add_it schemalist all_dnames typestr =
    (prs("Double elimination not implemented for mutual recursion \n");
    []);


fun do_inductive_type_double (safe:bool) (with_bindings(*ctxt_c*))  
                      (declaration_bindings(*ctxt_c*))
                      (schema_bindings(*ctxt_c*))
                      (is_relation:bool)
		      (typestr:cnstr_c) = 
  let
    val _ = message "** prove double elim rule **"
    val init_context = redo_bindings_with_dependency safe with_bindings
                                                     declaration_bindings
				                     schema_bindings
    val schema_list =
      nice_schemas (make_schema_list declaration_bindings schema_bindings)
    val disj_sch_list = make_disj_var_schemas schema_list
    val name_list = make_name_list declaration_bindings schema_bindings
  in
    (pr_cc (do_all schema_list (fst (hd name_list)) (snd (hd name_list))
       name_list typestr));
    ((init_context @ (eliminators name_list schema_list typestr)
     @ (add_it disj_sch_list name_list typestr)),
(* Only change is above here, schema_list replaced by disj_sch_list *)
     (if is_relation then (Prop_c) 
      else (make_reductions name_list disj_sch_list typestr)))
 end;


(* Works fine on nat and list *)
(* Need to change for: mutual recursion.....*not* properly handled yet,
   also check handling of inductive relations *)



(* The whole thing is......
   First lambda abstract by T,
   then by theta_rest applied to each possible pair of schemas
   
   now first elim, applied to T with first arg lambda abstracted
       and 2nd arg universally quantified.... 
                [z:intype]{z':indtype}T z z'
   now for each constructor we have a further nat-elim, applied
   to T partially instantiated with iota for that constructor
   and then applied to appropriate theta-rests....
   the nat_elim is lambda abstracted by each binder and arity and then
   each arity, the theta-rests are instantiated with these bindings *)
end end













