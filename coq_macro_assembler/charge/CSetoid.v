Require Import Setoid.
Require Import Morphisms.

Class Equiv (A : Type) := equiv : relation A.
Infix "===" := equiv (at level 70, no associativity).

Class type (A : Type) {e : Equiv A} := eq_equiv : Equivalence equiv.

(* allows setoid rewriting with types *)
Instance type_equiv {T} {e : Equiv T} {t : type T} : Equivalence equiv := eq_equiv.


(* setoid morphisms *)
Definition setoid_resp {T T'} (f : T -> T') `{e : type T} `{e' : type T'} :=
  forall x y, x === y -> f x === f y.

Record morphism T T' `{e : type T} `{e' : type T'} :=
  mkMorph {
    morph :> T -> T';
    morph_resp : setoid_resp morph}.

Implicit Arguments mkMorph [T T' e e0 e' e1].
Implicit Arguments morph_resp.

Infix "-s>" := morphism (at level 45, right associativity).
Ltac resp_set :=
  intros t1 t2 HEqt; repeat (intros ?); simpl in *; try rewrite !HEqt; reflexivity.

Section Morphisms.
  Context {S T U V} `{eS : type S} `{eT : type T} `{eU : type U} `{eV : type V}.

  Global Instance morph_equiv : Equiv (S -s> T) :=
    fun f g => forall x, f x === g x.

  Global Instance morph_type : type (S -s> T).
  Proof.
    split.
      intros f x; reflexivity.
      intros f g HS x; symmetry; apply HS.
    intros f g h Hfg Hgh x; etransitivity; [apply Hfg | apply Hgh].
  Qed.

  Program Definition mcomp (f: T -s> U) (g: S -s> T) : (S -s> U) :=
    mkMorph (fun x => f (g x)) _.
  Next Obligation.
    intros x y HEq; apply f, g; assumption.
  Qed.

  Global Instance equiv_morph :
    Proper (equiv ==> equiv ==> equiv) (morph S T).
  Proof.
    intros f g HEq x y HEq'; etransitivity; [apply HEq | apply g, HEq'].
  Qed.

End Morphisms.

Infix "<<" := mcomp (at level 35).

Section MorphConsts.
  Context {S T U V} `{eS : type S} `{eT : type T} `{eU : type U} `{eV : type V}.

  Global Instance equiv_mcomp :
    Proper (equiv (A := T -s> U) ==> equiv ==> equiv) mcomp.
  Proof.
    intros f f' HEq g g' HEq' x; simpl; rewrite HEq, HEq'; reflexivity.
  Qed.

  Lemma mcomp_assoc
    (f: U -s> V) (g: T -s> U) (h: S -s> T) : f << (g << h) === (f << g) << h.
  Proof. intros x; reflexivity. Qed.

  Definition lift2s (f : S -> T -> U) p q : (S -s> T -s> U) :=
    mkMorph (fun x => mkMorph (f x) (p x)) q.

  Definition lift3s (f : S -> T -> U -> V) p q r : (S -s> T -s> U -s> V) :=
    mkMorph (fun x => mkMorph (fun y => mkMorph (f x y) (p x y)) (q x)) r.

End MorphConsts.

Instance Equiv_PropP : Equiv Prop := iff.
Instance type_PropP : type Prop := iff_equivalence.

Section SetoidProducts.
  Context {A B : Type} `{eA : type A} `{eB : type B}.

  Global Instance Equiv_prod : Equiv (A * B) :=
    fun p1 p2 => (fst p1 === fst p2) /\ (snd p1 === snd p2).

  Global Instance prod_proper : Proper (equiv ==> equiv ==> equiv) (@pair A B).
  Proof.
    intros a a' Ha b b' Hb; split; assumption.
  Qed.

  Global Instance type_prod : type (A * B).
  Proof.
    split.
      intros [a b]; split; reflexivity.
      intros [a1 b1] [a2 b2] [Ha Hb]; split; symmetry; assumption.
    intros [a1 b1] [a2 b2] [a3 b3] [Ha12 Hb12] [Ha23 Hb23];
      split; etransitivity; eassumption.
  Qed.

  Global Instance mfst_proper : Proper (equiv ==> equiv) (@fst A B).
  Proof.
    intros [a1 b1] [a2 b2] [Ha Hb]; assumption.
  Qed.

  Global Instance msnd_proper : Proper (equiv ==> equiv) (@snd A B).
  Proof.
    intros [a1 b1] [a2 b2] [Ha Hb]; assumption.
  Qed.

  Program Definition mfst : (A * B) -s> A :=
    mkMorph (fun p => fst p) _.
  Next Obligation. resp_set. Qed.

  Program Definition msnd : (A * B) -s> B :=
    mkMorph (fun p => snd p) _.
  Next Obligation. resp_set. Qed.

  Context {C} `{eC : type C}.

  Program Definition mprod (f: C -s> A) (g: C -s> B) : C -s> (A * B) :=
    mkMorph (fun c => (f c, g c)) _.
  Next Obligation. resp_set. Qed.

  Lemma mprod_unique (f: C -s> A) (g: C -s> B) (h: C -s> A * B) :
    mfst << h === f -> msnd << h === g -> h === mprod f g.
  Proof.
    intros HL HR x; split; simpl; [rewrite <- HL | rewrite <- HR]; reflexivity.
  Qed.

End SetoidProducts.

Section IndexedProducts.

  Record ttyp := {carr :> Type; eqc : Equiv carr; eqok : type carr}.
  Global Instance ttyp_proj_eq {A : ttyp} : Equiv A := eqc A.
  Global Instance ttyp_proj_prop {A : ttyp} : type A := eqok A.
  Context {I : Type} {P : I -> ttyp}.

  Global Program Instance Equiv_prodI : Equiv (forall i, P i) :=
    fun p p' : forall i, P i => (forall i : I, @equiv _ (eqc _) (p i) (p' i)).

  Global Instance type_prodI : type (forall i, P i).
  Proof.
    split.
      intros X x; reflexivity.
      intros X Y HS x; symmetry; apply HS.
    intros X Y Z HPQ HQR x; etransitivity; [apply HPQ | apply HQR].
  Qed.

  Program Definition mprojI (i : I) : (forall i, P i) -s> P i :=
    mkMorph (fun X => X i) _.
  Next Obligation. 
    intros X Y HXY; apply HXY.
  Qed.

  Context {C : Type} `{eC : type C}.

  Program Definition mprodI (f : forall i, C -s> P i) : C -s> (forall i, P i) :=
    mkMorph (fun c i => f i c) _.
  Next Obligation. resp_set. Qed.

  Lemma mprod_projI (f : forall i, C -s> P i) i : mprojI i << mprodI f === f i.
  Proof. intros X; reflexivity. Qed.

  Lemma mprodI_unique (f : forall i, C -s> P i) (h : C -s> forall i, P i) :
    (forall i, mprojI i << h === f i) -> h === mprodI f.
  Proof.
    intros HEq x i; simpl; rewrite <- HEq; reflexivity.
  Qed.

End IndexedProducts.

Section Exponentials.

  Context {A B C D} `{eA : type A} `{eB : type B} `{eC : type C} `{eD : type D}.

  Program Definition comps : (B -s> C) -s> (A -s> B) -s> A -s> C :=
    lift2s (fun f g => f << g) _ _.
  Next Obligation. resp_set. Qed.
  Next Obligation. resp_set. Qed.

  Program Definition muncurry (f : A -s> B -s> C) : A * B -s> C :=
    mkMorph (fun p => f (fst p) (snd p)) _.
  Next Obligation. resp_set. Qed.

  Program Definition mcurry (f : A * B -s> C) : A -s> B -s> C :=
    lift2s (fun a b => f (a, b)) _ _.
  Next Obligation. resp_set. Qed.
  Next Obligation. resp_set. Qed.

  Definition mprod_map (f : A -s> C) (g : B -s> D) := mprod (f << mfst) (g << msnd).

  Program Definition meval : (B -s> A) * B -s> A :=
    mkMorph (fun p => fst p (snd p)) _.
  Next Obligation. resp_set. Qed.

  Program Definition mid : A -s> A := mkMorph (fun x => x) _.
  Next Obligation. resp_set. Qed.

  Program Definition mconst (b : B) : A -s> B := mkMorph (fun _ => b) _.
  Next Obligation. resp_set. Qed.

End Exponentials.

Section Exp_props.
  Context {A B C D} `{eA : type A} `{eB : type B} `{eC : type C} `{eD : type D}.

  Lemma mcurry_com (f : A * B -s> C) : f === meval << (mprod_map (mcurry f) mid).
  Proof. intros [a b]; reflexivity. Qed.

  Lemma mcurry_uniqe (f : A * B -s> C) h :
    f === meval << (mprod_map h mid) -> h === mcurry f.
  Proof. intros HEq a b; simpl; rewrite HEq; reflexivity. Qed.

End Exp_props.

Instance unit_Equiv : Equiv unit := (fun _ _ => True).
Instance unit_type : type unit.
Proof.
  split.
    intros x; exact I.
    intros x y _; exact I.
  intros x y z _ _; exact I.
Qed.

Inductive empty : Set := .
Instance empty_Equiv : Equiv empty := (fun _ _ => False).
Instance empty_type : type empty.
Proof.
  split; intros x; case x.
Qed.

Section Initials.
  Context {A} `{eA : type A}.

  Program Definition mzero_init : empty -s> A := mkMorph (fun x => match x with end) _.
  Next Obligation. intros x; case x; fail. Qed.

  Lemma mzero_init_unique (f g : empty -s> A) : f === g.
  Proof. intros x; case x. Qed.

End Initials.

Section Subsetoid.

  Context {A} `{eA : type A} {P : A -> Prop}.

  Global Instance subset_Equiv : Equiv {a : A | P a} :=
    fun x y => proj1_sig x === proj1_sig y.
  Global Instance subset_type : type {a : A | P a}.
  Proof.
    split.
      intros [x Hx]; red; red; reflexivity.
      intros [x Hx] [y Hy] HS; red; red; symmetry; exact HS.
    intros [x Hx] [y Hy] [z Hz] Hxy Hyz; red; red; etransitivity; [apply Hxy | apply Hyz].
  Qed.

  Global Instance proj1sig_proper :
    Proper (equiv (A := {a : A | P a}) ==> equiv (A := A)) (@proj1_sig A (fun x => P x)).
  Proof. intros [x Hx] [y Hy] HEq; simpl; apply HEq. Qed.

  Program Definition mforget : {a : A | P a} -s> A :=
    mkMorph (fun x => x) _.
  Next Obligation. resp_set. Qed.

  Context {B} `{eB : type B}.
  Program Definition minherit (f : B -s> A) (HB : forall b, P (f b)) : B -s> {a : A | P a} :=
    mkMorph (fun b => exist P (f b) (HB b)) _.
  Next Obligation.
    intros x y HEq; unfold equiv; red; simpl; rewrite HEq; reflexivity.
  Qed.

  Lemma mforget_mono (f g : B -s> {a : A | P a}) : mforget << f === mforget << g -> f === g.
  Proof.
    intros HEq x; red; red; simpl; rewrite (HEq x); reflexivity.
  Qed.

End Subsetoid.

Section Option.

  Context {A} `{eA : type A}.

  Global Instance option_Equiv : Equiv (option A) := fun x y =>
    match x, y with
      | None, None => True
      | Some x, Some y => x === y
      | _, _ => False
    end.

  Global Instance option_type : type (option A).
  Proof.
    split.
      intros [a |]; red; red; reflexivity.
      intros [a |] [b |] HS; red; red; exact I || contradiction HS || symmetry; exact HS.
    intros [a |] [b |] [c |] Hab Hbc; simpl in *; try (contradiction || exact I); [].
    red; red; etransitivity; [apply Hab | apply Hbc].
  Qed.

End Option.

Section OptDefs.
  Context {A B} `{eA : type A} `{eB : type B}.

  Global Instance Some_proper : Proper (equiv ==> equiv (A := option A)) (@Some A).
  Proof. intros a b HEq; simpl; apply HEq. Qed.

  Program Definition msome : A -s> option A := mkMorph (fun a => Some a) _.
  Next Obligation. resp_set. Qed.

  Program Definition moptionbind (f : A -s> option B) : option A -s> option B :=
    mkMorph (fun oa => match oa with None => None | Some a => f a end) _.
  Next Obligation.
    intros [x |] [y |] HEq; contradiction || trivial || apply f, HEq.
  Qed.

End OptDefs.
