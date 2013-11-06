Module lib_vectors Import lib_finite lib_list_length;

(* 
   $Log: lib_vectors.l,v $
   Revision 1.4  1998/10/30 16:58:58  ctm
   modified to use conditional visibility

   Revision 1.3  1997/11/12 20:02:42  djs
   Fixed a "tms fixes it, CVS breaks it again" log message problem.

   Revision 1.2  1997/11/02 17:12:06  tms
   o Replaced Immed by Try Immed
   o Added further Eliminatin Principles
   o Added vect_update function
   o Added characterisation theorem
*)

Inductive 
[vect:{n:nat}Type] ElimOver Type
Parameters 
[A?Type]
Constructors 
[vnil:vect zero]
[vcons:{a:A}{n|nat}{v:vect n}(vect (suc n))];

(* Vectors as an inductive type ... very similar to list *)

(* For defining functions on non-empty vectors such as extracting the head, it is convenient ot use a tailored elimination principle : *)
  
[C:{n|nat}{v:vect (suc n)}Type];
[vect_elim_ne_prem:{a:A}{n|nat}{v:vect n}C (vcons a v)];

$Goal vect_elim_ne_C : {n|nat}{v:vect n}Type;
Induction n;
  intros; Refine trueProp;	(* base case *)
  intros; Refine C v;
$Save vect_elim_ne_C;

Goal vect_elim_ne : {n|nat}{v:vect (suc n)}C v;
intros; 
Refine vect_elim vect_elim_ne_C ?? v;
  Intros; Immed;
  intros; Refine vect_elim_ne_prem;
Save vect_elim_ne;

Discharge C;

Goal {n:nat}{m:vect (suc n)}{P:(vect (suc n))->Type}
	({a:A}{m:vect n}P (vcons a m))->P m;
	intros _;
	Refine vect_elim 
              (nat_elim ([x:nat](vect x)->Type) ([_:vect zero]trueProp)
		([x|nat][_:(vect x)->Type][n = suc x][m:vect n]
		{P:(vect n)->Type}({a:A}{m:vect x}P (vcons a m))->P m));
	Intros; Try Immed;
	Intros; Refine H;
Save vect_elim'_lemma;


[vect_rec [C|Type] = vect_elim [n|nat][_:vect n]C];
[vect_iter [C|Type][a:C][f:nat->A->C->C] = 
               vect_rec a [x:A][n|nat][_:vect n]f n x];

[vect_ind [P:{n:nat}(vect n)->Prop] = vect_elim P];


Goal vnil_lemma : {n:nat}{v:vect n}(([n|nat]((nat_elim|([x:nat](vect x)->Prop)
           ([x=zero][v:vect zero](Eq v vnil))
           ([x:nat][_:((vect x)->Prop)][_:(vect (suc x))]trueProp)
           n):((vect n)->Prop))) v);
Refine vect_elim [n|nat]((nat_elim|([x:nat](vect x)->Prop)
           ([x=zero][v:vect zero](Eq v vnil))
           ([x:nat][_:((vect x)->Prop)][_:(vect (suc x))]trueProp)
           n):((vect n)->Prop));
Refine Eq_refl;
Intros;
Try Immed;
Save vnil_lemma;

Goal vect_zero_eq_vnil : {v:vect zero}(Eq v vnil);
intros;
Refine vnil_lemma zero;
Save vect_zero_eq_vnil;

(* Head of a non-empty vector *)
Goal vect_head : {n|nat}{m:vect (suc n)}A;
Refine vect_elim_ne [n|nat][m:vect (suc n)]A;
intros; Immed;
Save vect_head;


Goal vect_tail : {n|nat}{m:vect (suc n)}(vect n);
Refine vect_elim_ne [n|nat][m:vect (suc n)]vect n;
intros; Immed;
Save vect_tail;

Goal cons_inj_lemma1 : {a,b:A}{n:nat}{v:vect n}(Eq (vcons a v) (vcons b v))
          -> (Eq a b);
intros;
Refine Eq_subst H [x:vect (suc n)](Eq a (vect_head x));
Refine Eq_refl;
Save cons_inj_lemma1;


Goal cons_inj_lemma2 : {a:A}{n:nat}{v,w:vect n}(Eq (vcons a v) (vcons a w))
          -> (Eq v w);
intros;
Refine Eq_subst H [x:vect (suc n)](Eq v (vect_tail x));
Refine Eq_refl;
Save cons_inj_lemma2;


Goal vect_head_cons_tail : {n|nat}{v:vect (suc n)}(Eq (vcons (vect_head v) (vect_tail v)) v);
intros;
Refine vect_elim'_lemma n v [v:vect (suc n)]
           (Eq (vcons (vect_head v) (vect_tail v)) v);
intros;
Refine Eq_refl;
Save vect_head_cons_tail;

Goal vect_nth : {n|nat}{x:fin n}{v:vect n}A;
Induction x;
  Refine vect_head;
  intros; Refine x_ih (vect_tail v);
Save vect_nth;

Goal vect_update : {n|nat}{x:fin n}{v:vect n}{t:A}vect n;
Induction x;

  (* updating the first element *)
  intros; Refine vcons t (vect_tail v);

  (* updating another element *)
  intros; Refine vcons (vect_head v) (x_ih (vect_tail v) t);
Save vect_update;

(*
zeroth == (f_zero two) : (fin three);
first == f_suc (f_zero one) : (fin three);
second == f_suc (f_suc (f_zero zero)): (fin three);
[a,b,c,d:A];
test_vect == vcons a (vcons b (vcons c vnil)) : vect three;
test_vect2 == vcons d (vcons a (vcons c vnil)) : vect three;
vect_nth three first test_vect;
Normal VReg;
vect_nth three zeroth test_vect;
Normal VReg;
vect_nth three second test_vect;
Normal VReg;

vect_nth three first test_vect2;
Normal VReg;
vect_nth three zeroth test_vect2;
Normal VReg;
vect_nth three second test_vect2;
Normal VReg;
*)


$Goal vect_character_rhs : {n:nat}{v:vect n}vect n;
Induction n;
  intros; Refine vnil;
  intros; Refine vcons (vect_head v) (vect_tail v);
$Save vect_character_rhs;

Goal vect_character : {n|nat}{v:vect n}Eq v (vect_character_rhs n v);
Induction v Then intros Then Refine Eq_refl;
Save vect_character;


Goal vect_zip : {n:nat}{bin:A->A->A}(vect n) -> (vect n) -> (vect n);
intros __;
Refine nat_elim ([n:nat](vect n)->(vect n)->vect n);
intros;
Refine vnil;
intros;
Refine vcons;
Refine bin (vect_head H) (vect_head H1);
Refine x1_ih;
Refine vect_tail H; 
Refine vect_tail H1; 
Save vect_zip;


(*
[a,b,c,d:A];
[bin:A->A->A];

test1 == vcons a (vcons c vnil);
test2 == vcons b (vcons d vnil);
vect_zip two bin test1 test2;
Normal VReg;
*)
(*
Inductive [list:Type]
Parameters [B:Type]
Constructors
[nil:list]
[cons:{a:B}{l:list}list];
Discharge B;
*)

Goal vector_to_list : {n|nat}(vect n) -> (list A);
Refine vect_elim ([n|nat][v:vect n]list A);
Refine nil A;
intros;
Refine cons|A a v_ih;
Save vector_to_list;

Goal vector_to_list_resp_cons : {n|nat}{v:vect n}{a:A}(Eq (cons|A a (vector_to_list v))
                               (vector_to_list (vcons a v)));
Refine vect_ind [n|nat][v:vect n]({a:A}Eq (cons|A a (vector_to_list v)) (vector_to_list (vcons a v)));
intros;
Refine Eq_refl;
intros;
Refine Eq_resp;
Refine v_ih;
Save vector_to_list_resp_cons;


Goal vect_nth_equiv_nth : {n|nat}{x:fin n}{v:vect n}{a:A}
       (Eq (vect_nth x v) (nth (fin_to_nat x) (vector_to_list v) a));
intros _;
Refine nat_ind [n:nat]{x:fin n}{v:vect n}{a:A}(Eq (vect_nth x v) (nth (fin_to_nat x) (vector_to_list v) a));
intros;
Refine zero_set_is_empty x;
intros;
Qrepl Eq_sym (vect_head_cons_tail v);
Qrepl Eq_sym (vector_to_list_resp_cons (vect_tail v) (vect_head v));
Refine finite_is_zero_or_succ n1 x;
intros;
Qrepl H1;
Refine Eq_refl;
intros;
Refine H1; intros;
Qrepl H2;
Qrepl Eq_sym (fin_to_nat_resp_suc t);
Refine H;
Save vect_nth_equiv_nth;

Discharge A;
