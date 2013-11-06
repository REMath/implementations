Module lib_quotient Import lib_eq_basics;

(* Contents
   --------
   o Martin Hofmann's quotient types
*)

(* General comment on quotient types. There doesn't seem to be a
genuinely inductive definition of quotient types. We will always need
one or the other axiom which cannot be reduced. the idea in this
approach is to make use of the fact that in ECC propositions and types
are completely separated. So assuming certain propositions to be
inhabited does not affect the computational types. This means that
even in the nonempty context which is defined below every element of
the natural numbers reduces to canonical form.

Logical consistency of quotient types can be proven semantically.
Indeed in every topos model of ECC the assumption ext_prop and those
concerning the quotient types are inhabited. 

My ultimate goal, however, is to justify quotient types by a syntactic
translation into the pure type theory. Each proof made using quotient
types will then automatically be translated into one using
"book-equality". Hopefully this will be achieved end of May *)


(* Assume equality of if and only if propositions *)
$[ext_prop:{X,Y:Prop}(X->Y)->(Y->X)->Eq X Y];

(* Assume a set together with a prop valued equivalence relation on it *)
[A|Type(0)];
[R:A->A->Prop];
[R_refl:refl R][R_sym:sym R][R_trans:trans R];

(* For any such set we introduce the "quotient type", ie a set of
nonempty equivalence classes *)

$[QU:Type(0) // R]

(* QU_class associates the corresponding equivalence class to an element 
of a *)
$[QU_class:A->QU];

(* We assume that related elements have equal equivalence classes *)
$[QU_cor:{a1,a2:A}(R a1 a2) -> Eq (QU_class a1) (QU_class a2)]

(* To define a function on the quotient type one must give it on the
underlying set and provide a proof that it is well defined on
equivalence classes *)

$[QU_it:{C|Type}{f:A->C}({a1,a2:A}(R a1 a2) -> (Eq (f a1) (f a2))) -> QU -> C];

(* Axiom stating that QU_class is surjective *)
$[QU_ind:{P:QU->Prop}({a:A}P(QU_class a)) -> {q:QU}P q];

(* A computation rule for quotient type. If a lifted function gets
applied to a canonical element then the underlying algorithm will be
executed *)

[[C|Type][f:A->C][H:{a1,a2:A}(R a1 a2) -> Eq (f a1) (f a2)][a:A]
 QU_it f H (QU_class a) ==> f a];


(* Proof that QU_it respects extensional equality *)

Goal QU_xi : {C|Type}{f,g:A->C}
     {p:{a1,a2:A}(R a1 a2) -> Eq (f a1)(f a2)}
     {q:{a1,a2:A}(R a1 a2) -> Eq (g a1)(g a2)}
     ({a:A}Eq (f a) (g a)) -> {x:QU} Eq (QU_it f p x) (QU_it g q x); 
Intros C f g p q H;
Refine QU_ind [x:QU]Eq (QU_it f p x) (QU_it g q x);
Immed;
Save QU_xi;


(* Induction principle for QU_it *)
Goal QU_it_ind : {C|Type}{P:C->Prop}{f:A->C}
     {p:{a1,a2:A}(R a1 a2) -> Eq (f a1)(f a2)}
     ({a:A}P (f a)) -> {x:QU}P (QU_it f p x);
Intros C P f p H;
Refine QU_ind [x:QU]P (QU_it f p x);
Immed;
Save QU_it_ind;

(* The rest of this file is devoted to the proof that Q (QU_class
x)(QU_class y) implies that x and y are related by R. It is only here
that the assumption that R be an equivalence relation is actually
needed. The quotient type can be defined without this assumption. then
it becomes the quotient by the reflexive symmetric transitive closure
*)

[a,b:A][Hab:Eq (QU_class a) (QU_class b)];

Goal QU_in_class : QU -> Prop;
Refine QU_it;
Refine R a;
Intros a1 a2 Ra1a2;
Refine ext_prop;
Intros Raa1;
Refine R_trans;
Immed;
Intros Raa2;
Refine R_trans;
Immed;
Refine R_sym;
Immed;
SaveUnfrozen QU_in_class;

Goal QU_cor_inv : R a b;
Equiv QU_in_class (QU_class b);
Qrepl (Eq_sym Hab);
Refine R_refl;
Save QU_cor_inv;
Discharge A;






