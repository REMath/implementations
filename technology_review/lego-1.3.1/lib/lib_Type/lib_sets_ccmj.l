Module lib_sets_ccmj Import lib_logic;

(* Contents
   --------
   o A representation of set theory
*)

(* A Set is a type, with an equality relation *)

(* We use eq to denote this relation *)

[A|Type];
[eq|A -> A -> Prop];
eq_refl == {x|A}eq x x;
eq_sym == {x,y|A}(eq x y) -> (eq y x);
eq_trans == {x,y,z|A}(eq x y) -> (eq y z) -> (eq x z);
Discharge eq;
eq_rel == <eq:A->A->Prop>and3 (eq_refl|eq) (eq_sym|eq) (eq_trans|eq);
Discharge A;
set == <A:Type><eq:A->A->Prop>
     and3 (eq_refl|A|eq) (eq_sym|A|eq) (eq_trans|A|eq);

[A|set];
eq == A.2.1;
Discharge A;

(* So eq is the name given to equality on a set, the set
   often to be inferred from the context *)

[A|set];
eq_refl_ax == and3_out1 A.2.2;
Goal eq_sym_ax : {x,y|A.1}(eq x y) -> (eq y x); 
Intros x y; Refine and3_out2 A.2.2; Save eq_sym_ax;
Goal eq_trans_ax : {x,y,z|A.1}(eq x y) -> (eq y z) -> (eq x z);
Intros x y z; Refine and3_out3 A.2.2; Save eq_trans_ax;
Discharge A;

[A,B|set];
(* A function from A to B is a function on the types
   which respects equality *)

[f:A.1 -> B.1];
pres_eq == {x,y|A.1}(eq x y) -> (eq (f x) (f y));
Discharge A;

[A,B:set];
function == <f:A.1 -> B.1>(pres_eq|A|B f);
Discharge A;

[A,B|set];
[f|(function A B)];
pres_eq_ax == f.2;
Discharge A;

(* We could give names to the carrier of the set, also
   to the carrier of a function but for now we will
   just use the projections *)

(* Simple set theory -- e.g. the cartesian product *)

[A,B|set];

pr [x:(A.1)][y:(B.1)] == (x,y);
Discharge A;

[A,B:set];
Goal cross_prod : set;
Intros#;
Refine <a:A.1>B.1;
Intros#;
Intros x y;
Refine and (eq x.1 y.1) (eq x.2 y.2);
Refine pair3;
Intros x;
Refine pair;
Refine eq_refl_ax;
Refine eq_refl_ax;
Intros x y h1;
Refine pair;
Refine eq_sym_ax (fst h1);
Refine eq_sym_ax (snd h1);
Intros x y x h1 h2; Refine pair;
Refine eq_trans_ax (fst h1) (fst h2);
Refine eq_trans_ax (snd h1) (snd h2);
SaveUnfrozen cross_prod;
Discharge A;

(* Functions of two variables *)

[A,B,C:set];
[f:function|(cross_prod A B)|C];

Goal curry : A.1 -> B.1 -> C.1;
Intros a b;
Refine f.1 (pr a b);
Save curry;
Discharge A;

(* Composition of two functions is a function *)
[A,B,C|set]
[f:function A B];
[g:function B C];
Goal comp : function A C;
Intros#;
Intros a; Refine g.1; Refine f.1;Refine a;
Intros x y h1;
Refine pres_eq_ax;
Refine pres_eq_ax;
Refine h1;
Save comp;
Discharge A;

(* So comp is polymorphic composition of functions *)


(* Relations on a set *)

[A:set];
[Rel:A.1 -> A.1 -> Prop];
pres_l == {x,y,z:A.1}(eq x y) -> (Rel x z) -> (Rel y z);
pres_r == {x,y,z:A.1}(eq x y) -> (Rel z x) -> (Rel z y);
Discharge Rel;

relation == <R:A.1 -> A.1 ->Prop>and (pres_l R)(pres_r R);
Discharge A;

[A|set];
[R|relation A];
rel_pres_eq_l == fst R.2;
rel_pres_eq_r == snd R.2;
Discharge A;

(* We want to be able to talk about forming
  families (collections) of things   *)

(* can do via subsets, given as injective maps *)
(* We now get rid of the injectiveness, so a subset
   is just the range of some function *)

subset[A:set] == A.1 -> Prop;

(*
(* Show that any A->Prop which respects eq gives a subset *)
[A:set];
[k:A.1 -> Prop];
(* [resp:{x,y:A.1}(eq x y) -> (k x) -> (k y)];  we don't need
this....why ? because we really use k' where k' x iff
there exists y and y=x and k y *)
Goal proptosubset : subset A;
Intros#;
Refine <x:A.1>(k x);
(* Now prove this is a set *)
Intros x;
Refine x.1;
Save proptosubset;
Discharge A;
*)

(* We especially want this notion to cope with
   'constructing families' i.e. for each x in A
   and r in Re, take the ball (x,r) sort of
   stuff, hopefully this will expedite things   *)

(* inject is now the polymorphic injection which in the context of
   a subset X of a set A, takes something of type X.1 into A.1 *)
(* And inj_pres_eq is the theorem that eq x y -> eq (inj x) (inj y) *)




[A,B:set];
[f:A.1 -> A.1 -> B.1];
pres_eq2 == {x,y,z|A.1}(eq x y) -> 
           (and (eq (f x z) (f y z)) (eq (f z x) (f z y)));
Discharge f;
function2 == <f:A.1 -> A.1 -> B.1>(pres_eq2 f);

Discharge A;

[A,B|set];
[f|function2 A B];

Goal pres_eq_l : {x,y,z:A.1}(eq x y) -> (eq (f.1 x z) (f.1 y z));
intros;
Refine fst (f.2 H);
Save pres_eq_l;

Goal pres_eq_r : {x,y,z:A.1}(eq x y) -> (eq (f.1 z x) (f.1 z y));
intros;
Refine snd (f.2 H);
Save pres_eq_r;

Discharge A;













