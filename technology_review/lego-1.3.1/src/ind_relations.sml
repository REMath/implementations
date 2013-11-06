(* ind_relations.sml *)

functor FunInductive (structure Concrete:CONCRETE
		      structure Namespace:NAMESPACE) (* : INDUCTIVE *) =
    struct
	local
	    open Concrete
	    open Namespace
	in
	    type cnstr_c=Concrete.cnstr_c

(* tidying up code -- no major changes *)

(* Modified version of datatype.sml to get something for inductive
   relations *)

(* Signature of this module is the function do_inductive_type which takes
   3 ctxt_c lists and a boolean and returns a ctxt_c list
   paired with a reduction   *)

(* schema_head is not just a string, but a string
   applied to some arguments.... *)
datatype schema_head =
  Head of string |
  Appl_a of prntVisSort * schema_head * cnstr_c;

(* This is a variant on the concrete syntax cnstr_c
   in parser.sml; with account taken of schema
   variables *)
  
datatype schema_c =
  Ref_s of schema_head  (* A schema variable *)
| Bind_s of binder_c * schema_c  (* Simple binding (x:K) where
				  K is not a schema *)
| Bind_sc of binder_s * schema_c  (* Complex binding by a schema *)
withtype binder_c =
    bindSort * visSort * frzLocGlob * string list * string list * cnstr_c
and binder_s =
    bindSort * visSort * frzLocGlob * string list * string list * schema_c;

exception sch_err of string;


fun binders_ind (Bind_c((_,d,_,_,l,s1),s)) = 
      (map (fn x => (x,s1,d)) l)@(binders_ind s)
  | binders_ind (_) = [];
  
(* outputs a (string,constr_c) list  *)

fun start_T_of_C l  str = 
       foldl  (fn x => (fn (a,_,d) =>
                           App_c((prVis d),x,Ref_c(a)))) (Ref_c(str)) l;
       
fun T_of_C l str typestr= 
  fold  (fn ((a,b,_),x) => Bind_c((Pi,Hid,(UnFroz,Local),[],[a],b),x))
   l (Bind_c((Pi,Vis,(UnFroz,Local),[],[""],(start_T_of_C l str)),(typestr)));
          
 
(* The type of ``C'' for an inductive type str with binders l *)

fun start_A_of_C l str = 
   foldl  (fn x => (fn (a,_,_) => App_c(NoShow,x,Ref_c(a))))
   (Ref_c("C_"^str)) l;

fun Univer_of_C l str =
  foldr (fn (a,b,_) => (fn x => Bind_c((Pi,Hid,(UnFroz,Local),[],[a],b),x)))
  (Bind_c((Pi,Vis,(UnFroz,Local),[],["z"],(start_T_of_C l str)),
            App_c(ShowNorm,(start_A_of_C l str),Ref_c("z")))) l;

(* For debugging *)  

fun pr_cc c = ();   (***************************************)
val rec pr_app =
  fn Head(str) => prs str
  |  Appl_a(_,a,c) =>( pr_app a; prs" "; pr_cc c);
  
  
val rec pr_sc =
 fn Ref_s(str) => pr_app str 
  | Bind_s((_,_,_,_,y,c),d) => 
         (prs"(B," ;prs(hd y);prs":";pr_cc c;prs"'";pr_sc d;prs")")
  | Bind_sc((_,_,_,_,x,c),d) => 
         (prs"(B," ;prs(hd x);prs":";pr_sc c;prs"'";pr_sc d;prs")");


fun appl_to_type (Head(s)) = Ref_c(s) |
    appl_to_type (Appl_a(x,a,c)) = App_c(x,(appl_to_type a),c);
    
fun schema_to_type (Ref_s(s)) = appl_to_type(s) |
    schema_to_type (Bind_s(b,s)) = Bind_c(b,(schema_to_type s)) |
    schema_to_type (Bind_sc((a,b,c,l,m,s1),s2)) =
    Bind_c((a,b,c,l,m,(schema_to_type s1)),(schema_to_type s2));
  
fun get_names [] = [] |
    get_names (((_,_,_,_,l,_):binder_c)::rest) = 
    l @ (get_names rest);

(* Supposed to massage bindings into appropriate form.
   Do everything with Global for now... *)

(* We can re-use get schema names to get names of
   types to make dependencies *)

fun get_end_type (Bind_c(_,s)) = get_end_type s
 |  get_end_type (Ref_c(s)) = Ref_c(s)
 |  get_end_type (Type_c(s)) = Type_c(s)
 |  get_end_type (Prop_c) = Prop_c
 |  get_end_type (TypeAbs_c(n)) = TypeAbs_c(n)
 |  get_end_type _ = raise sch_err "Unexpected type";
      
fun subst_for_type st (Bind_c(x,s)) = Bind_c(x,(subst_for_type st s))
 |  subst_for_type st (Type_c("")) = Type_c(st)
 |  subst_for_type st _ = raise sch_err "Unexpected type";


fun get_end (Bind_c(_,s)) = get_end s
 |  get_end (App_c(_,s,_)) = get_end s
 |  get_end (Ref_c(s)) = s
 |  get_end _ = raise sch_err "Unexpected type";

fun look_up_type cn dn_binds =
   let val find_it = get_end cn
   in 
     foldr
        (fn (_,_,_,_,str,cn2) =>
            (fn x =>
               if mem find_it str then 
                   get_end_type cn2 
             else x))
     (Type_c(""))
     dn_binds end;
     
(* (Let,Def,(UnFroz,Local),[],["T"],Type_c) *)


fun do_cast cast_to (Bind_c((a,b,c,d,l,cn),rest)) =
      Bind_c((a,b,c,d,l,(Cast_c(cn,cast_to))),(do_cast cast_to rest)) |
      do_cast cast_to x = x;

fun redo_bindings_with_dependency (safe:bool) (with_bindings:binder_c list)
    (declaration_bindings:binder_c list) (schema_bindings:binder_c list) =
     let val dependent_names = get_names schema_bindings;
     val (new_declaration_bindings) =
        foldr (fn (a,b,_,d,l,cn):binder_c =>
              (fn so_far:(binder_c list) =>
        if (get_end_type cn = Type_c("")) then
        ((map (fn name => 
           (a,b,(UnFroz,Global),d@dependent_names,[name],
	    subst_for_type name cn)) l)
	 @so_far)
        else 
       ((a,b,(UnFroz,Global),d@dependent_names,l,cn)::so_far)))
       ([])
       declaration_bindings;
    (* a should always be Let and cn Type (or maybe Prop...) here *)
     val new_schema_bindings =
          map (fn (a,b,_,m,l,cn) => 
                   (a,b,(UnFroz,Global),m,l,
          (if safe then
             (do_cast (look_up_type cn new_declaration_bindings) cn )
             else cn) ))
          schema_bindings 
     in
       (with_bindings@new_declaration_bindings@new_schema_bindings) (*: binder_c list *)
     end;

 
(* No need for contexts here *)

(* So what we need is a function to convert the 3 concrete
   terms given as input to the datatype into schema_c,
   calculate from the schema_c terms the cnstr_c terms
   which make up the elimination and reduction rules,
   massage the bindings to get right dependency on the
   original 3 concrete bits and pass back 
    (1) The list of bindings (The type, its constructors and
   the elimination rule)
    (2) The reduction (another constr_c)
*)

(* A function to test whether or not a term contains
   the schema variable, first argument is the list of
   schema variables *)

fun contains l (Prop_c)         = false |
    contains l (Type_c(_))      = false |
    contains l (TypeAbs_c(_))   = false |
    contains l (Ref_c(x))       = mem x l|
    contains l (App_c(_,c1,c2)) = (contains l c1) orelse (contains l c2) |
    contains l (Bind_c((_,_,_,_,l1,c1),c2)) =
     (contains (filter_neg (fn x => mem x l1) l) c1) 
                                  orelse (contains l c2)  |
    contains l (Tuple_c (l1,c)) = (contains l c) orelse 
       foldr (fn x => (fn y => contains l x orelse y)) false l1 |
    contains l (Proj_c(p,c))    = contains l c |
    contains l (Cast_c(c1,c2))  = (contains l c1) orelse (contains l c2) |
    contains l (Var_c(_))   = raise sch_err "Metavariables not allowed here" |
    contains l NewVar_c     = raise sch_err "Metavariables not allowed here" |
    contains l Bot_c        = false |
    contains l _            = raise sch_err "error in contains";


fun make_type_nice n (Bind_c((a,b,c,d,l,s1),s)) = 
      let fun name n = ("x"^string_of_num n);
          fun chck_list n [] = (n,[]) |
                  chck_list n (a::l) = 
                       let val (m1,l1) = chck_list n l in
                             if (a = "") 
                                then (succ m1,((name m1)::l1))
		                else (m1,(a::l1)) end; 
         val (new_n,new_l) = chck_list n l  in           
	     (Bind_c((a,b,c,d,new_l,s1),(make_type_nice new_n s))) end |
	     make_type_nice n x = x;
  
	     

fun free_in_binder_list l ([](*:ctxt_c*)) = false |
    free_in_binder_list l ((_,_,_,_,l1,c1)::rest)  =
    ((contains (filter_neg (fn x => mem x l1) l) c1))
    orelse (free_in_binder_list l rest);
  
fun make_name_list [] s_binds = [] |
    make_name_list (((_,_,_,_,l,c):binder_c)::rest) s_binds =
    (map (fn x => let fun mnrec m =
	  let val nn = x^string_of_num m
       in if (free_in_binder_list ["C_"^nn] s_binds) then mnrec (succ m) 
	  else nn end;
              val nice_c = make_type_nice 1 c
		  in
          if (free_in_binder_list ["C_"^x] s_binds) then
         ((mnrec 1),nice_c) else (x,nice_c) end)
        l)@(make_name_list rest s_binds);

(* Substitution of b for a in concrete term c is
   subst (a,b) c *)

fun subst_c l (Prop_c)         = Prop_c |
    subst_c l (Type_c(s))         = Type_c(s) |
    subst_c l (TypeAbs_c(x))   = TypeAbs_c(x) |
    subst_c (a,b) (Ref_c(x))   = if a=x then Ref_c(b) else Ref_c(x) |
    subst_c l (App_c(x,c1,c2)) = 
              App_c(x,(subst_c l c1),(subst_c l c2)) |
    subst_c (a,b) (Bind_c((x,y,c,d,l1,c1),c2)) =
                  if (mem a l1) then Bind_c((x,y,c,d,l1,c1),c2)
      else Bind_c((x,y,c,d,l1,(subst_c (a,b) c1)),(subst_c (a,b) c2)) |
    subst_c l (Tuple_c(l1,c)) = Tuple_c(map (fn x => (subst_c l x)) l1,
					(subst_c l c))  |
    subst_c l (Proj_c(p,c))   = Proj_c(p,subst_c l c) |
    subst_c l (Cast_c(c1,c2)) = Cast_c((subst_c l c1),(subst_c l c2)) |
    subst_c l (Var_c(_)) = raise sch_err "Metavariables not allowed here" |
    subst_c l NewVar_c   = raise sch_err "Metavariables not allowed here" |
    subst_c l Bot_c      = Bot_c |
    subst_c l _          = raise sch_err "error in subst_c";

(* Similarly, but for schemas too *)

fun subst_app l (Head(x)) = Head(x) |
    subst_app l (Appl_a(x,a,c)) = Appl_a(x,(subst_app l a),subst_c l c);
    

fun subst_s l (Ref_s(x)) = Ref_s(subst_app l x) |
    subst_s (a,b) (Bind_s((x,y,c,d,l1,c1),s2)) =
         if (mem a l1) then  Bind_s((x,y,c,d,l1,c1),(subst_s (a,b) s2))
         else Bind_s((x,y,c,d,l1,(subst_c (a,b) c1)),(subst_s (a,b) s2)) |
    subst_s (a,b) (Bind_sc((x,y,c,d,l1,s1),s2)) =
         if (mem a l1) then  Bind_sc((x,y,c,d,l1,s1),(subst_s (a,b) s2))
         else Bind_sc((x,y,c,d,l1,(subst_s (a,b) s1)),(subst_s (a,b) s2));

fun subst_c_list [] cnstr = cnstr |
    subst_c_list (s::l) cnstr = subst_c_list l (subst_c s cnstr);
    
fun subst_s_list [] cnstr = cnstr |
    subst_s_list (s::l) cnstr = subst_s_list l (subst_s s cnstr);

fun make_disj_var_schema schema n =
   let fun name str n = let
             fun mnrec m =
                 let val nn = str^string_of_num m
                 in if (mem nn n) then mnrec (succ m) 
                            else nn end in
				mnrec 1 end;
       fun chck_list n [] = ([],n,[]) |
           chck_list n (a::l) = 
                let val (subs,m1,l1) = chck_list n l in
                if mem a m1 then     
                  let val newname = name a m1 in
                   ((a,newname)::subs,newname::m1,newname::l1) end 
               else (subs,a::m1,a::l1)  end;
       fun chck_names n ((a,b,c,l,m,cn)) = 
	   let val (subs,n1,m1) = 
                   chck_list n m in (subs,n1,(a,b,c,l,m1,cn)) end;
       fun sort_schema n (Ref_s(mm)) = (n,Ref_s(mm)) |
           sort_schema n (Bind_s(b,cn)) =
           let val (ss,m,nb) = chck_names n b;
	       val (m1,nsc) = sort_schema m cn
               in (m1,Bind_s(nb,(subst_s_list ss nsc))) end |
           sort_schema n (Bind_sc(b,sch)) =
	   let val (ss,m,(a,b,c,l,g,cn)) = chck_names n b ;
               val (m1,nsc) = sort_schema m cn;
	       val (m2,sc) = sort_schema m1 sch
          in (m2,Bind_sc((a,b,c,l,g,(subst_s_list ss nsc)),sc)) end 
   in  sort_schema n schema end;

(*  
val sche = Bind_s((Pi,Vis,(UnFroz,Local),[],["a"],Ref_c("A")),
    Bind_s((Pi,Vis,(UnFroz,Local),[],["x"],Ref_c("a")),Ref_s("list")));
    *)

fun make_disj_var_schemas schema_list =
   let fun do_stuff [] = ([],[]) |
           do_stuff ((str,S)::rest) =
           let val (n,nrest) = do_stuff rest;
               val (m,nschema) =  make_disj_var_schema S n   
                    in
	       (m,((str,nschema)::nrest)) end;
       val (x,nschema_list) = do_stuff schema_list
   in nschema_list end;

(* This function should convert a term in cnstr_c into
   a schema term given the list of schematic variables l *)

fun map_cnstr_to_appl l (Ref_c(x)) = if mem x l then Head(x) else
          raise sch_err "Not a valid schema" |
    map_cnstr_to_appl l (App_c(x,c,c1)) =
           if (contains l c1) then raise sch_err "Not a valid schema"
	   else Appl_a(x,(map_cnstr_to_appl l c),c1) |
    map_cnstr_to_appl l _ =  raise sch_err "Not a valid schema";
	
	   
fun map_cnstr_to_schema l (Bind_c((Pi,b,c,l1,l2,c1),c2)) =
        if (contains l c1) then 
                Bind_sc((Pi,b,c,l1,l2,(map_cnstr_to_schema l c1)),
		        (map_cnstr_to_schema l c2))
        else
            Bind_s((Pi,b,c,l1,l2,c1),(map_cnstr_to_schema l c2))
  | map_cnstr_to_schema l (Ref_c(s))     =
      if mem s l then Ref_s(Head(s))
      else raise sch_err "Not a valid schema"
  | map_cnstr_to_schema l (App_c(x,a,b)) =
      Ref_s(map_cnstr_to_appl l (App_c(x,a,b)))
  | map_cnstr_to_schema l _ = raise sch_err "Not a valid schema";
	 

fun make_schema_list (declaration_bindings(*:ctxt_c*)) 
       (schema_bindings (*:ctxt_c*)) =
    let val names = get_names declaration_bindings in
    foldr (fn ((a,b,c,_,l,cn):binder_c) => (fn rest =>
       (let val S = (map_cnstr_to_schema names cn) in
       (map (fn x => (x,S)) l) end)@rest)) nil
    schema_bindings
    end;

fun make_schema_nice schema n =
   let fun name n = ("x"^string_of_num n);
       fun chck_list n [] = (n,[]) |
           chck_list n (a::l) = 
                 let val (m1,l1) = chck_list n l in
                      if (a = "") 
                      then (succ m1,((name m1)::l1))
		      else (m1,(a::l1)) end;
       fun chck_names n ((a,b,c,l,m,cn)) = 
	   let val (n1,m1) = chck_list n m in (n1,(a,b,c,l,m1,cn)) end;
       fun sort_schema n (Ref_s(mm)) = (n,Ref_s(mm)) |
           sort_schema n (Bind_s(b,cn)) =
           let val (m,nb) = chck_names n b;
	       val (m1,nsc) = sort_schema m cn
               in (m1,Bind_s(nb,nsc)) end |
           sort_schema n (Bind_sc(b,sch)) =
	   let val (m,(a,b,c,l,g,cn)) = chck_names n b ;
               val (m1,nsc) = sort_schema m cn;
	       val (m2,sc) = sort_schema m1 sch
                   in (m2,Bind_sc((a,b,c,l,g,nsc),sc)) end 
   in  sort_schema n schema end;

(*  
val sche = Bind_s((Pi,Vis,(UnFroz,Local),[],["",""],Ref_c("A")),
    Bind_sc((Pi,Vis,(UnFroz,Local),[],["",""],Ref_s("list")),Ref_s("list")));
    *)

fun nice_schemas schema_list =
   let fun do_stuff [] = (1,[]) |
           do_stuff ((str,S)::rest) =
           let val (n,nrest) = do_stuff rest;
               val (m,nschema) = make_schema_nice S n   
                    in
	       (m,((str,nschema)::nrest)) end;
       val (x,nschema_list) = do_stuff schema_list
   in nschema_list end;

      
(* Also want this to make a name up if l2 is "" or list of them 
  since this is needed in phizero *)

fun strictly_positive (Ref_s(_)) = true |
    strictly_positive (Bind_s(_,s)) = strictly_positive s |
    strictly_positive (Bind_sc(_,_)) = false;
  
fun valid_schema (Ref_s(_)) = true |
    valid_schema (Bind_s(_,s)) = valid_schema s  |
    valid_schema (Bind_sc((_,_,_,_,_,s1),s)) = valid_schema s  
    andalso strictly_positive s1;

fun arities (Ref_s(_)) = [] |
    arities (Bind_s(_,s)) = arities s |
    arities (Bind_sc((_,y,_,_,l,s1),s)) = 
                      (map (fn x => (x,y,s1)) l)@(arities s);

fun binders (Ref_s(_)) = [] |
    binders (Bind_s((_,y,_,_,l,s1),s)) = 
      (map (fn x => (x,y,s1)) l)@(binders s) |
    binders (Bind_sc((_,y,_,_,l,s1),s)) = 
    (map (fn x => (x,y,(schema_to_type s1))) l)@(binders s);

fun gen_app z y (s::nil) = App_c((prVis y),z,Ref_c(s)) |
    gen_app z y (s::l) = gen_app (App_c((prVis y),z,Ref_c(s))) y l |
    gen_app z _ _ = raise sch_err "Something very wrong here";
    
fun get_name_app (Head(s)) = s |
    get_name_app (Appl_a(x,a,c)) = get_name_app a;

fun phizero (Ref_s(s)) z = App_c(ShowNorm,Ref_c("C_"^(get_name_app s)),z)
  | phizero (Bind_s((Pi,x,_,_,l,c),c1)) z =
                     Bind_c((Pi,x,(UnFroz,Local),[],l,c),
                 (phizero c1 (gen_app z x l)))
  | phizero _ z = raise sch_err "Schema is not strictly positive";
		     
fun phihash (Ref_s(s)) f z = App_c(ShowNorm,f,z) |
    phihash (Bind_s((Pi,x,_,_,l,c),c1)) f z =
            Bind_c((Lda,x,(UnFroz,Local),[],l,c),
                      (phihash c1 f (gen_app z x l))) |
       phihash _ f z = raise sch_err "Schema is not strictly positive";

fun get_name_and_type (Ref_s(s)) = (get_name_app s,s) |
    get_name_and_type (Bind_s(_,s)) = get_name_and_type(s) |
    get_name_and_type (Bind_sc(_,s)) = get_name_and_type(s) ;  
  
fun iota_of_a (x,S) = 
   foldl
  (fn cnstr => (fn (name,x,cnstr2) =>
   (App_c((prVis x),cnstr,Ref_c(name)))))
   (Ref_c(x)) (binders S);
(*   
fun start_up c str ty l = 
    let
	fun stuff [] z = z |
	    stuff ((na,x,_)::m) z = 
	    stuff m (App_c((prVis x),z,Ref_c(na)));  
    in 
	App_c(ShowNorm,(apply_all (args_of_head ty) 
                    (Ref_c("C_"^str))),(stuff l c)) end;
*)	
(* Bug in start_up....sorted out now  *)	
fun start_up S z str ty = 
     App_c(ShowNorm,(Ref_c("C_"^str)),(iota_of_a (z,S)));
     
fun thetazero S z =
  let 
    val l1 = binders S;
    val (name,ty) = get_name_and_type S;
    val l2 = arities S
  in
    let val begin = foldr 
      (fn (str,x,schema) =>
       (fn so_far => Bind_c((Pi,x,(UnFroz,Local),[],[str^"_ih"],
			     (phizero schema (Ref_c(str)))),
			    so_far)))
      (start_up S z name ty)
      l2
    in 
      foldr (fn (name,x,cnstr) => fn so_far =>
	     Bind_c((Pi,x,(UnFroz,Local),[],[name],cnstr),so_far))
      begin
      l1
    end 
  end;
		    
fun eliminator schema_names name type_of_name list_of_schemas typestr =
    let val name_l = binders_ind type_of_name;
	val start_value = Univer_of_C name_l name;
	val innerpart =
	  (foldr (fn (str,schema) =>
		  (fn rest => Bind_c((Pi,Vis,(UnFroz,Local),[],[""],
				      (thetazero schema str)),rest)))
	   start_value 
	   list_of_schemas)
    in
      foldr (fn (str,cnstr) =>
	     (fn rest => Bind_c((Pi,Vis,(UnFroz,Local),[],["C_"^str],
				 (T_of_C (binders_ind cnstr) str typestr)),
				rest)))
      innerpart
      schema_names
    end;

fun eliminators schema_names list_of_schemas typestr =
  map (fn (str,cnstr) => 
       (Lda,Vis,(UnFroz,Global),[],[str^"_elim"],
	(eliminator schema_names str cnstr list_of_schemas typestr)):binder_c)
  schema_names;
  
(* Need to elaborate ``schema_names'' so as to retain the
   type information from which derives type of ``C'' *)

(* Need something to force an argument into every Pi binding
   in a schema else create one... *)

fun first_bindings name_list typestr = 
   map (fn (str,cnstr) => 
    (Lda,Vis,(UnFroz,Local),[],["C_"^str],
     (T_of_C (binders_ind cnstr) str typestr)):binder_c) name_list;

fun second_bindings schema_list =
    map (fn (str,schema) =>  
    (Lda,Vis,(UnFroz,Local),[],[mkNameGbl("f_"^str)], 
     (thetazero schema str)):binder_c)
    schema_list;

fun third_bindings schema_list =
   foldr (fn (a,S) => (fn x => 
        (map (fn (name,y,cnstr) => 
     (Lda,y,(UnFroz,Local),[],[name],cnstr):binder_c) (binders S))@x)) nil 
   schema_list;
   
fun all_bindings name_list schema_list typestr =
   ListUtil.flatten [first_bindings name_list typestr,second_bindings schema_list,
		   third_bindings schema_list]

(* takes a constructor name and its schema and gives back
   what Luo calls ``\iota(bar{a})'', a cnstr_c '' *)

(* Should have eliminated the rev by using foldl...check this ! *)


fun recursor_applied_to_bindings name_list schema_list (x,S) =
  let val (str,ty) = get_name_and_type S
  in
     (foldl (fn cnstr => (fn (name,schema)
			  => (App_c(ShowNorm,cnstr,Ref_c(mkNameGbl("f_"^name)))))) 
      (foldl (fn cnstr => (fn (name,cnstr2) =>
			   (App_c(ShowNorm,cnstr,Ref_c("C_"^name)))))
       (Ref_c((str)^"_elim")) name_list)
      schema_list)
  end;

fun lhs_of_reduction name_list schema_list (x,S) =
  App_c(ShowNorm,  
	(recursor_applied_to_bindings name_list schema_list (x,S)),
	(iota_of_a(x,S)));
  
fun rhs_of_reduction name_list schema_list (x,S) =
  foldl 
  (fn cnstr =>
   (fn (name,y,schema) =>
    App_c((prVis y),cnstr,(phihash schema   
			   (recursor_applied_to_bindings
			    name_list schema_list (name,schema))
			   (Ref_c(name)))))) 
  (foldl
   (fn cnstr =>
    (fn (name,y,cnstr2) =>
     (App_c((prVis y),cnstr,(Ref_c(name))))))
   (Ref_c(mkNameGbl("f_"^x))) (binders S))
  (arities S);

fun make_reductions name_list schema_list typestr=
     Red_c((all_bindings name_list schema_list typestr),
   (map (fn (x,S) => 
     ((lhs_of_reduction name_list schema_list (x,S)),
      (rhs_of_reduction name_list schema_list  (x,S))))
    schema_list));
    

fun do_old_inductive_type (safe:bool) (with_bindings(*:ctxt_c*))
                      (declaration_bindings(*:ctxt_c*))
                      (schema_bindings(*:ctxt_c*))
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
  in
    ((init_context @ (eliminators name_list schema_list typestr)),
     (if is_relation then (Prop_c) 
      else (make_reductions name_list disj_sch_list typestr)))
 end;

(**********************
fun do_inductive_type (with_bindings(*:ctxt_c*))
                      (declaration_bindings(*:ctxt_c*))
                      (schema_bindings(*:ctxt_c*))
                      (is_relation:bool) (typestr:cnstr_c) = 
      do_old_inductive_type false with_bindings declaration_bindings
      schema_bindings is_relation typestr;
      
fun do_safe_inductive_type (with_bindings(*:ctxt_c*))
                      (declaration_bindings(*:ctxt_c*))
                      (schema_bindings(*:ctxt_c*))
                      (is_relation:bool) (typestr:cnstr_c) = 
      do_old_inductive_type true with_bindings declaration_bindings
      schema_bindings is_relation typestr;
**********************)
end end
