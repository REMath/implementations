Require Export Utf8.

Module Equiv.
  Class t (A:Type) : Type := Make  {
    eq : A -> A -> Prop;
    refl : ∀ x, eq x x;
    sym : ∀ x y, eq x y -> eq y x;
    trans : ∀ x y z, eq x y -> eq y z -> eq x z
  }.
End Equiv.
Local Notation "x == y" := (Equiv.eq x y) (at level 40).

Module Poset.
  Class t A : Type := Make  {
    eq :> Equiv.t A;
    order : A -> A -> Prop;
    refl : ∀ x y,  x==y -> order x y;
    antisym : ∀ x y, order x y -> order y x -> x==y;
    trans : ∀ x y z, order x y -> order y z -> order x z
  }.
End Poset.
Notation "x ⊑ y" := (Poset.order x y) (at level 40).

Class subset A `{Equiv.t A} : Type := SubSet
  { carrier : A -> Prop;
    subset_comp_eq : ∀ x y:A, x==y ->  carrier x -> carrier y}.
Coercion carrier : subset >-> Funclass.

Module CompleteLattice.
  Class t (A:Type) : Type := Make
  { porder :> Poset.t A;
    join : subset A -> A;
    join_bound : ∀x:A, ∀f:subset A, f x -> x ⊑ join f;
    join_lub : ∀f:subset A, ∀z, (∀ x:A, f x -> x ⊑ z) -> join f ⊑ z
  }.
Definition subset_meet A {L:t A} (S:subset A) : subset A.
refine (SubSet A _ (fun a => ∀x:A, S x -> a ⊑ x) _).
intros.
apply Poset.trans with x; auto.
apply Poset.refl; apply Equiv.sym; auto.
Defined.
Definition meet {A} {L:t A} (S:subset A) : A := join (subset_meet A S).

Lemma meet_bound : forall A (L:t A),
  ∀x:A, ∀f:subset A, f x -> (meet f) ⊑ x.
Proof.
  unfold meet; intros.
  apply join_lub; intros.
  simpl in H0 ; auto.
Qed.

Lemma meet_glb : forall A (L:t A),
  ∀f:subset A, ∀z, (∀ x, f x -> z ⊑ x) -> z ⊑ meet f.
Proof.
  unfold meet; intros.
  apply join_bound; simpl; intros; auto.
Qed.
End CompleteLattice.

Hint Resolve @Equiv.refl @Equiv.sym @Equiv.trans
             @Poset.refl @Poset.antisym @Poset.trans
             @CompleteLattice.join_bound @CompleteLattice.join_lub
             @CompleteLattice.meet_bound @CompleteLattice.meet_glb.

Instance ProductEquiv {A B} (Ea : Equiv.t A) (Eb : Equiv.t B) : Equiv.t (A * B).
refine (Equiv.Make (A * B) (fun x y => @Equiv.eq _ Ea (fst x) (fst y) /\ @Equiv.eq _ Eb (snd x) (snd y)) _ _ _);
firstorder;
eauto.
Defined.

Instance ProductPoset {A B} (Pa: Poset.t A) (Pb: Poset.t B) : Poset.t (A * B).
refine (Poset.Make (A*B) (ProductEquiv _ _) (fun x y => @Poset.order _ Pa (fst x) (fst y) /\ @Poset.order _ Pb (snd x) (snd y)) _ _ _); firstorder;
eauto.
Defined.

Definition left_subset {A B} (Ea:Equiv.t A) (Eb:Equiv.t B) (f:subset (A*B)) : subset A.
refine (SubSet A Ea (fun a => exists b, f (a,b)) _).
intros x y Heq [b Hb].
exists b.
refine (@subset_comp_eq _ _ f (x,b) (y,b) _ Hb).
split; simpl; auto.
Defined.

Definition right_subset {A B} (Ea:Equiv.t A) (Eb:Equiv.t B) (f:subset (A*B)) : subset B.
refine (SubSet B Eb (fun b => exists a, f (a,b)) _).
intros x y Heq [a Ha].
exists a.
refine (@subset_comp_eq _ _ f (a,x) (a,y) _ Ha).
split; simpl; auto.
Defined.

Instance ProductCompleteLattice {A B} (La: CompleteLattice.t A) (Lb: CompleteLattice.t B) : CompleteLattice.t (A * B).
refine (CompleteLattice.Make (A*B) (ProductPoset _ _) (fun f => (@CompleteLattice.join _ La (left_subset _ _ f), @CompleteLattice.join _ Lb (right_subset _ _ f))) _ _).
intros [a b] f Hf.
split; simpl;
apply CompleteLattice.join_bound;[exists b|exists a];
exact Hf.
intros f [a b] H.
split;
apply CompleteLattice.join_lub; simpl; intros x [x' Hx'];
apply (H _ Hx').
Defined.

Notation "'℘' A" := (A -> Prop) (at level 10).

Instance PowerSetEquiv A : Equiv.t (℘ A).
refine (Equiv.Make (A -> Prop) (fun P Q => ∀ x, (P x <-> Q x)) _ _ _); firstorder.
Defined.

Instance PowerSetPoset A : Poset.t (℘ A).
refine (Poset.Make (A -> Prop) (PowerSetEquiv _) (fun P Q => ∀ x, (P x -> Q x)) _ _ _); firstorder.
Defined.

Instance PowerSetCompleteLattice A : CompleteLattice.t (℘ A).
refine
  (CompleteLattice.Make (A -> Prop) (PowerSetPoset _)
    (fun Q => fun x => exists y, Q y /\ y x) _ _); firstorder.
Defined.

Instance PointwiseEquiv {A L} `(Equiv.t L) : Equiv.t (A->L).
refine (Equiv.Make _ (fun P Q => ∀ x, (P x) == (Q x)) _ _ _); firstorder.
eauto.
Defined.

Instance PointwisePoset A {L} `(Poset.t L) : Poset.t (A->L).
refine (Poset.Make _ (PointwiseEquiv _) (fun P Q => ∀ x, (P x) ⊑ (Q x)) _ _ _); firstorder.
eauto.
Defined.

Definition proj {L A} `{CompleteLattice.t L} `(Q:subset (A->L)) (x:A) : subset L.
refine (SubSet _ _ (fun y => exists P, Q P /\ y == (P x)) _).
intros.
destruct H2 as [P [H1' H2]].
exists P; split; eauto.
Defined.

Instance PointwiseCompleteLattice A {L} `(CompleteLattice.t L) : CompleteLattice.t (A->L).
refine (CompleteLattice.Make (A->L) (PointwisePoset A _)
  (fun f: subset (A->L) => fun x:A => CompleteLattice.join (proj f x)) _ _).
repeat intro.
apply @CompleteLattice.join_bound.
simpl.
eauto.
repeat intro.
apply @CompleteLattice.join_lub.
simpl; intros.
destruct H1 as [P [T1 T2]].
apply Poset.trans with (P x); auto.
apply H0; auto.
Defined.

Class monotone A `{Poset.t A} B `{Poset.t B} (f: A → B) : Prop :=
  mon_prop : ∀ a1 a2, a1 ⊑ a2 -> f a1 ⊑ f a2.

Instance PointwiseMonotoneEquiv A B `(Poset.t A) `(Poset.t B) : Equiv.t { f | monotone A B f } :=
  {| eq F1 F2 := ∀ x y, x == y → proj1_sig F1 x == proj1_sig F2 y |}.
Proof.
  intros (); auto.
  intros (); auto.
  intros (); eauto.
Defined.

Instance PointwiseMonotonePoset A B `(Poset.t A) `(Poset.t B) : Poset.t { f | monotone A B f } :=
  {| order F1 F2 := ∀ x, proj1_sig F1 x ⊑ proj1_sig F2 x |}.
Proof.
  auto.
  intros (f&F)(g&G) L R x y E. simpl in *. apply Poset.antisym; eauto.
  eauto.
Defined.

Module Join.
  Class t {A} `(Poset.t A) : Type := Make  {
    op : A -> A -> A;
    join_bound1 : ∀x y:A, x ⊑ op x y;
    join_bound2 : ∀x y:A, y ⊑ op x y;
    join_least_upper_bound : ∀x y z:A, x ⊑ z -> y ⊑ z -> (op x y) ⊑ z
  }.
End Join.
Notation "x ⊔ y" := (Join.op x y) (at level 40).

Module Meet.
  Class t {A} `(Poset.t A) : Type := Make  {
    op : A -> A -> A;
    meet_bound1 : ∀x y:A, op x y ⊑ x;
    meet_bound2 : ∀x y:A, op x y ⊑ y;
    meet_greatest_lower_bound : ∀x y z:A, z ⊑ x -> z ⊑ y -> z ⊑ (op x y)
  }.
End Meet.
Notation "x ⊓ y" := (Meet.op x y) (at level 40).

Module Bot.
  Class t {A} `(Poset.t A) : Type := Make  {
    elem : A;
    prop : forall x : A, elem ⊑ x
  }.
End Bot.
Notation "⊥" := (Bot.elem) (at level 40).

Module Top.
  Class t {A} `(Poset.t A) : Type := Make  {
    elem : A;
    prop : forall x : A, x ⊑ elem
  }.
End Top.
Notation "⊤" := (Top.elem) (at level 40).

Module Lattice.
  Class t (A:Type) : Type := Make
  { porder :> Poset.t A;
    join :> Join.t porder;
    meet :> Meet.t porder;
    bot :> Bot.t porder;
    top :> Top.t porder
  }.
End Lattice.
Hint Resolve
   @Join.join_bound1 @Join.join_bound2 @Join.join_least_upper_bound
   @Meet.meet_bound1 @Meet.meet_bound2 @Meet.meet_greatest_lower_bound
   @Bot.prop @Top.prop.

(* Some results about complete lattices *)
Definition empty {L} `{CL:CompleteLattice.t L} : subset L.
apply SubSet with (fun x : L => False).
intuition.
Defined.

Definition bottom {L} `{CL:CompleteLattice.t L} : L := CompleteLattice.join empty.

Lemma bottom_is_bottom : forall L `{CL:CompleteLattice.t L}, ∀x:L, bottom ⊑ x.
Proof.
  unfold bottom; intros; apply CompleteLattice.join_lub; intros.
  destruct H.
Qed.

Definition top {L} `{CL:CompleteLattice.t L} : L := CompleteLattice.meet empty.

Lemma top_is_top : forall L `{CL:CompleteLattice.t L}, ∀x:L, x ⊑ top.
Proof.
  unfold top; intros; apply CompleteLattice.meet_glb; auto; intros.
  destruct H.
Qed.

Instance PowerSetBot (A:Type) : Bot.t (PowerSetPoset A).
refine (Bot.Make _ (PowerSetPoset A) (fun _ => False) _).
simpl; intuition.
Defined.

Instance PowerSetTop (A:Type) : Top.t (PowerSetPoset A).
refine (Top.Make _ (PowerSetPoset A) (fun _ => True) _).
simpl; intuition.
Defined.

Instance PowerSetJoin (A:Type) : Join.t (PowerSetPoset A).
refine (
  Join.Make _ (PowerSetPoset A) (fun X1 X2 a => X1 a \/ X2 a) _ _ _);
firstorder.
Defined.

Instance PowerSetMeet (A:Type) : Meet.t (PowerSetPoset A).
refine (
  Meet.Make _ (PowerSetPoset A) (fun X1 X2 a => X1 a /\ X2 a) _ _ _);
firstorder.
Defined.

Instance PowerSetLattice (A:Type) : Lattice.t (℘ A) := Lattice.Make _ _ _ _ _ _.

Instance PointwiseBot (A:Type) B PB (Bot:@Bot.t B PB) : @Bot.t (A->B) _.
refine (Bot.Make (A->B) _ (fun a:A => ⊥) _).
repeat intro.
apply Bot.prop.
Defined.

Instance PointwiseTop (A:Type) B PB (top:@Top.t B PB) : @Top.t (A->B) _.
refine (Top.Make (A->B) _ (fun a:A => ⊤) _).
repeat intro.
apply Top.prop.
Defined.

Instance PointwiseJoin (A:Type) B PB `(J:@Join.t B PB) : Join.t (PointwisePoset A PB).
refine (
  Join.Make _ _ (fun X1 X2 a => X1 a ⊔ X2 a) _ _ _);
repeat intro; auto.
Defined.

Instance PointwiseMeet (A:Type) B PB `(J:@Meet.t B PB) : Meet.t (PointwisePoset A PB).
refine (
  Meet.Make _ _ (fun X1 X2 a => X1 a ⊓ X2 a) _ _ _);
repeat intro; auto.
Defined.

Instance PointwiseLattice (A:Type) B (L:Lattice.t B) : Lattice.t (A->B) := Lattice.Make _ _ _ _ _ _.

Instance ProductLattice A B `{Lattice.t A} `{Lattice.t B} : Lattice.t (A*B).
apply (Lattice.Make (A*B) (ProductPoset _ _)).
apply Join.Make with (fun x y => (Join.op (fst x) (fst y), Join.op (snd x) (snd y)));
intuition; simpl; intuition; firstorder.
apply Meet.Make with (fun x y => (Meet.op (fst x) (fst y), Meet.op (snd x) (snd y)));
intuition; simpl; intuition; firstorder.
apply Bot.Make with (Bot.elem, Bot.elem);
intuition; simpl; auto.
apply Top.Make with (Top.elem, Top.elem);
intuition; simpl; auto.
Defined.

Definition PostFix {L P} f `(F:@monotone L P L P f) :  subset L.
apply SubSet with (fun a:L => (f a) ⊑ a); intros.
apply Poset.trans with x; auto.
apply Poset.trans with (f x); auto.
Defined.

Section Knaster_Tarski.

Definition lfp {L} `{CompleteLattice.t L} {f} (F:monotone L L f) : L :=
  CompleteLattice.meet (PostFix f F).

Variable L : Type.
Variable CL : CompleteLattice.t L.

Section f.
Variable (f: L → L) (F: monotone L L f).

(* Knaster-Tarski theorem *)
Lemma lfp_fixpoint : f (lfp F) == lfp F.
Proof.
  assert ((f (lfp F)) ⊑ (lfp F)).
  unfold lfp; apply CompleteLattice.meet_glb; intros.
  apply Poset.trans with (f x); auto.
  apply Poset.antisym; auto.
  unfold lfp; apply CompleteLattice.meet_bound.
  simpl.
  apply mon_prop; auto.
Qed.

Lemma lfp_least_fixpoint : ∀ x, f x == x -> lfp F ⊑ x.
Proof.
  intros.
  unfold lfp; apply CompleteLattice.meet_bound; simpl; auto.
Qed.


Lemma lfp_postfixpoint : f (lfp F) ⊑ lfp F.
Proof.
  unfold lfp; repeat intro.
  generalize (lfp_fixpoint); auto.
Qed.

Lemma lfp_least_postfixpoint : ∀x, f x ⊑ x -> lfp F ⊑ x.
Proof.
  unfold lfp; intros; auto.
Qed.

End f.

Lemma lfp_monotone : ∀ f1 f2 : L → L,
                     ∀ F1: monotone _ _ f1,
                     ∀ F2: monotone _ _ f2,
                       f1 ⊑ f2 -> lfp F1 ⊑ lfp F2.
Proof.
  intros.
  apply (lfp_least_postfixpoint f1); intros; auto.
  apply Poset.trans with (f2 (lfp F2)); auto.
  apply lfp_postfixpoint.
Qed.

End Knaster_Tarski.
