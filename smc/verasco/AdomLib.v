Require Import
  Utf8 String Bool
  ToString
  Maps
  LatticeSignatures.

Set Implicit Arguments.

(** * Adding a bottom element to an abstract domain **)
Inductive botlift (A:Type) : Type := Bot | NotBot (x:A).
Implicit Arguments Bot [A].
Notation "t +⊥" := (botlift t) (at level 39).

Definition bot {A: Type} (l: weak_lattice (A +⊥)) : A+⊥ := Bot.

Instance lift_bot_wl {A:Type} (l:weak_lattice A) : weak_lattice (A+⊥) :=
{ leb :=
    (fun x y =>
      match x, y with
        | Bot, _ => true
        | NotBot x, NotBot y => leb x y
        | _, _ => false
      end);
  top := (NotBot top);
  join :=
    (fun x y =>
      match x, y with
        | Bot, _ => y
        |_ , Bot => x
        | NotBot x, NotBot y => NotBot (join x y)
      end);
  widen :=
    (fun x y =>
      match x, y with
        | Bot, _ => y
        |_ , Bot => x
        | NotBot x, NotBot y => NotBot (widen x y)
      end)
}.

Instance lift_gamma (A B: Type) (G: gamma_op A B) : gamma_op (A+⊥) B :=
    (fun x =>
      match x with
      | Bot => fun _ => False
      | NotBot x => γ x
      end).

Definition lift_bot {A B:Type} WL G (l:adom A B WL G) : adom (A+⊥) B _ _.
Proof.
  split.
  (* gamma_monotone *)
  destruct a1; destruct a2; simpl; intuition; try congruence.
  apply (gamma_monotone l H); auto.
  (* gamma_top *)
  intros; simpl; apply gamma_top; auto.
  (* join sound *)
  intros [|x] [|y]; simpl; intuition; apply join_sound; auto.
Qed.

Definition botbind {A B} (f: A → B+⊥) (a: A+⊥) : B+⊥ :=
  match a with
    | Bot => Bot
    | NotBot x => f x
  end.

Notation "'do' X <- A ; B" := (botbind (fun X => B) A)
 (at level 200, X ident, A at level 100, B at level 200)
 : botbind_monad_scope.

Notation "'do_bot' X <- A ; B" := (botbind (fun X => B) A)
 (at level 200, X ident, A at level 100, B at level 200).

Lemma botbind_spec {A A' B B':Type} {GA: gamma_op A A'} {GB: gamma_op B B'} :
  ∀ f:A→B+⊥, ∀ x y, (∀ a, x ∈ γ a -> y ∈ γ (f a)) ->
                     (∀ a, x ∈ γ a -> y ∈ γ (botbind f a)).
Proof (λ f x y H a,
       match a with
       | Bot => λ K, K
       | NotBot a' => λ K, H _ K
       end).

Definition botbind2 {A B C} (f: A → B → C+⊥) (a: A+⊥) (b: B+⊥) : C+⊥ :=
  botbind (fun x => botbind (f x) b) a.

Lemma botbind2_spec {A A' B B' C C':Type} {AD:gamma_op A A'} {BD:gamma_op B B'} {CD:gamma_op C C'}:
  ∀ f:A→B→C+⊥, ∀ x y z, (∀ x_ab y_ab, x ∈ γ x_ab -> y ∈ γ y_ab -> z ∈ γ (f x_ab y_ab)) ->
                        (∀ x_ab y_ab, x ∈ γ x_ab -> y ∈ γ y_ab -> z ∈ γ (botbind2 f x_ab y_ab)).
Proof.
  unfold botbind2. repeat (intros; eapply botbind_spec; eauto).
Qed.

Definition botlift_fun1 {A B:Type} (f:A->B) (x:A+⊥) : B+⊥ :=
  botbind (@NotBot _ ∘ f) x.

Lemma botlift_fun1_spec {A A' B B':Type} {AD:gamma_op A A'} {BD:gamma_op B B'}:
  ∀ f:A→B, ∀ x y, (∀ x_ab, x ∈ γ x_ab -> y ∈ γ (f x_ab)) ->
                  (∀ x_ab, x ∈ γ x_ab -> y ∈ γ (botlift_fun1 f x_ab)).
Proof.
  unfold botlift_fun1. intros. eapply botbind_spec, H0. apply H.
Qed.

Definition botlift_fun2 {A B C:Type} (f:A->B->C) (a:A+⊥) (b:B+⊥) : C+⊥ :=
  botbind (fun x => botlift_fun1 (f x) b) a.

Lemma botlift_fun2_spec {A A' B B' C C':Type} {AD:gamma_op A A'} {BD:gamma_op B B'} {CD:gamma_op C C'}:
  ∀ f:A→B→C, ∀ x y z, (∀ x_ab y_ab, x ∈ γ x_ab -> y ∈ γ y_ab -> z ∈ γ (f x_ab y_ab)) ->
                      (∀ x_ab y_ab, x ∈ γ x_ab -> y ∈ γ y_ab -> z ∈ γ (botlift_fun2 f x_ab y_ab)).
Proof.
  unfold botlift_fun2. intros; eapply botbind_spec; eauto. intros; eapply botlift_fun1_spec; eauto.
Qed.

Instance bot_lift_toString A `{ToString A} : ToString (A+⊥) :=
  { to_string x := match x with
                   | Bot => "⊥"%string
                   | NotBot x' => to_string x'
                   end
  }.

Lemma union_list_bot A B WL G {AD: adom A B WL G} (z: A) (l: list (A+⊥)) :
  union_list (NotBot z) join l = Bot →
  ∀ x, List.In x l → x = Bot.
Proof.
  unfold union_list.
  destruct l as [|a l]. discriminate.
  induction l as [|b l IH] using List.rev_ind.
  simpl. intros -> [|x]; intuition discriminate.
  rewrite List.fold_left_app.
  intros H.
  assert (∀ a b: A+⊥, a ⊔ b = Bot → a = Bot ∧ b = Bot) as K.
  intros [|] [|]; simpl; auto; discriminate.
  destruct (K _ _ H) as (U & ->).
  specialize (IH U).
  intros x [->|L]. now apply IH; left.
  rewrite List.in_app_iff in L. destruct L as [L|[->|()]].
  now apply IH; right.
  easy.
Qed.

Lemma union_list_leb A (bot: A) join l (leb: A → A → bool) :
  (∀ x a b, leb x a = true ∨ leb x b = true → leb x (join a b) = true) →
  ∀ x,
    (l = nil → leb x bot = true) →
    (∃ y, List.In y l ∧ leb x y = true) →
    leb x (union_list bot join l) = true.
Proof.
  intros J. unfold union_list.
  destruct l as [|a l]. intuition.
  intros x _. revert x.
  induction l as [|b l IH] using List.rev_ind.
  simpl. intros x (y & [->|()] & H). easy.
  intros y (z & [->|IN] & H); rewrite List.fold_left_app; apply J.
  left; apply IH; exists z; intuition.
  rewrite List.in_app_iff in IN.
  destruct IN as [IN|[->|()]].
  left; apply IH; exists z; intuition.
  intuition.
Qed.

(** * Direct product of two abstract domains *)
Module WProd.
Section lat.
  Context {t1 t2 B: Type}.
  Context WL1 G1 (lat1 : adom t1 B WL1 G1).
  Context WL2 G2 (lat2 : adom t2 B WL2 G2).
  
  Definition A: Type := (t1*t2)%type.
  
  Definition leb: A -> A -> bool :=
    fun x y =>
      let (x1,x2) := x in
      let (y1,y2) := y in
        (leb x1 y1
      &&
        leb x2 y2)%bool.
  
  Definition top: A :=
    (top, top).
  
  Definition join: A -> A -> A :=
    fun x y =>
      let (x1,x2) := x in
      let (y1,y2) := y in
        (join x1 y1,
          join x2 y2).
  
  Definition widen: A -> A -> A :=
    fun x y =>
      let (x1,x2) := x in
      let (y1,y2) := y in
        (widen x1 y1,
          widen x2 y2).
  
  Definition gamma: A -> B -> Prop :=
    fun x =>
      let (x1,x2) := x in
      γ x1 ∩ γ x2.

  Lemma  gamma_monotone: forall a1 a2,
    leb a1 a2 = true -> gamma a1 ⊆ gamma a2.
  Proof.
    destruct a1; destruct a2; simpl.
    rewrite Bool.andb_true_iff in *.
    destruct 1.
    intros b [T1 T2].
    split; eapply gamma_monotone; eauto.
  Qed.
  
  Lemma gamma_top: forall x, gamma top x.
  Proof.
    simpl; split; apply gamma_top; auto.
  Qed.

  Lemma join_sound: forall x y, gamma x ∪ gamma y ⊆ gamma (join x y).
  Proof.
    intros (a,b)(c,d) q.
    simpl. intuition; apply join_sound; intuition.
  Qed.

  Instance make_wl : weak_lattice A :=
   {leb := leb;
    top := top;
    join := join;
    widen := widen
   }.

  Lemma make : adom A B _ gamma.
  Proof.
    split.
    exact gamma_monotone.
    exact gamma_top.
    exact join_sound.
  Qed.

End lat.
End WProd.

(** * Abstract domain of pairs of concrete elements. *)
Module WTensor.
Section lat.
  Context {t1 t2 B1 B2: Type}.
  Context WL1 G1 (lat1 : adom t1 B1 WL1 G1).
  Context WL2 G2 (lat2 : adom t2 B2 WL2 G2).
  
  Definition A: Type := (t1*t2)%type.
  Definition B: Type := (B1*B2)%type.
  
  Existing Instance WProd.make_wl.
  Instance gamma : gamma_op A B :=
    fun x y =>
      let (x1,x2) := x in
      let (y1,y2) := y in
      y1 ∈ γ x1 /\ y2 ∈ γ x2.

  Lemma  gamma_monotone: forall a1 a2,
    leb a1 a2 = true -> gamma a1 ⊆ gamma a2.
  Proof.
    destruct a1; destruct a2; simpl.
    rewrite Bool.andb_true_iff in *.
    destruct 1.
    intros [b1 b2] [T1 T2].
    split; eapply gamma_monotone; eauto.
  Qed.
  
  Lemma gamma_top: forall x, gamma top x.
  Proof.
    intros [b1 b2]; split; apply gamma_top; auto.
  Qed.

  Lemma join_sound: forall x y, gamma x ∪ gamma y ⊆ gamma (join x y).
  Proof.
    intros (a,b)(c,d) (b1,b2). simpl.
    intuition; apply join_sound; intuition.
  Qed.

  Lemma make : adom A B _ gamma.
  Proof.
    split.
    exact gamma_monotone.
    exact gamma_top.
    exact join_sound.
  Qed.

  Instance toString `{ToString t1} `{ToString t2} : ToString (t1 * t2) :=
    { to_string x := let '(a,b) := x in ("(" ++ to_string a ++ " ⊗ " ++ to_string b ++ ")")%string }.

End lat.
End WTensor.

(** * Exponentiation of an abstract domain to an abstract domain of total environments *)
Module WPFun (P:TREE). 
Module PP := Tree_Properties P.

Section lat.
Context {t0 B: Type}.
Context WL G (lat : adom t0 B WL G).

Definition t := P.t t0.
  (* [get m x = None] means [x = Top] *)

Definition bot : t+⊥ := Bot.

Definition top : t :=  (P.empty _).

Definition get (m: t) (r: P.elt) : t0 := 
  match P.get r m with
    | None => ⊤
    | Some i => i
  end.

Definition set (m: t) (r: P.elt) (i:t0) : t := P.set r i m.

Definition leb0 (m1 m2:t) : bool :=
  PP.for_all m2 (fun x i2 => leb (get m1 x) i2).

Lemma leb_le: forall m1 m2,
  leb0 m1 m2 = true -> (forall p, (get m1 p) ⊑ (get m2 p) = true
                                  \/ get m2 p = ⊤).
Proof.
  simpl; intros; 
  unfold leb0 in *; auto.
  rewrite PP.for_all_correct in H.
  unfold get in *.
  case_eq (P.get p m2); auto.
Qed.

Definition join : t -> t -> t := 
  P.combine
    (fun x y =>
       match x, y with
         | None, _ => None
         |_ , None => None
         | Some x, Some y => Some (join x y)
       end).

Definition widen: t -> t -> t := 
  P.combine 
    (fun x y =>
       match x, y with
         | None, _ => None
         |_ , None => None
         | Some x, Some y => Some (widen x y)
       end).

Instance gamma : gamma_op t (P.elt -> B) :=
  fun m rs =>
  forall r, γ (get m r) (rs r).

Lemma gamma_monotone: forall x y,
  leb0 x y = true ->
  gamma x ⊆ gamma y.
Proof.
  unfold gamma. intros x y H a H0 r.
  destruct (leb_le H r) as [K|K].
  eapply gamma_monotone; eauto.
  rewrite K; apply gamma_top; auto.
Qed.

  Lemma join_correct : forall (x y:t) b,
    gamma x b \/ gamma y b -> gamma (join x  y) b.
  Proof.
    unfold gamma, get; simpl; intros; unfold join.
    rewrite P.gcombine; auto.
    destruct H; generalize (H r);
    destruct (P.get r x); destruct (P.get r y);
    intros; first [ apply gamma_top | apply join_sound]; auto.
  Qed.

Instance make_wl : weak_lattice t :=
  { leb := leb0
  ; top := top
  ; join := join
  ; widen := widen
  }.

Lemma make : adom t (P.elt -> B) make_wl gamma.
Proof.
  split.
  exact gamma_monotone.
  (* gamma_top *)
  unfold γ, gamma, top, get; simpl; intros.
  rewrite P.gempty; apply gamma_top; auto.
  exact join_correct.
Qed.

Lemma gamma_set1 : forall (app:t) rs ab x,
  γ app rs ->
  γ ab (rs x) ->
  γ (set app x ab) rs.
Proof.
  simpl. unfold γ, gamma, set, get; intros.
  rewrite P.gsspec; destruct P.elt_eq; auto.
  subst; apply H0.
Qed.

Lemma gamma_set2 : forall (app:t) rs ab v x,
  γ app rs ->
  γ ab v ->
  γ (set app x ab) (fun p => if P.elt_eq p x then v else rs p).
Proof.
  simpl. unfold γ, gamma, set, get; intros.
  rewrite P.gsspec; destruct P.elt_eq; auto.
Qed.

Definition forget (app: t) (r: P.elt) : t := P.remove r app.

Lemma gamma_forget : forall (app:t) rs rs' x,
  γ app rs ->
  (forall y, x<>y -> rs y = rs' y) ->
  γ (forget app x) rs'.
Proof.
  simpl; unfold γ, gamma, forget, get; intros.
  specialize (H r).
  rewrite P.grspec; destruct P.elt_eq.
  apply gamma_top; auto.
  rewrite <- H0; auto.
Qed.

Lemma gamma_app: forall (m: t) (rs: P.elt -> B),
  γ m rs -> 
  forall r, γ (get m r) (rs r).
Proof.
  auto.
Qed.

Instance toString `{ToString P.elt} `{ToString t0} : ToString (P.t t0) :=
  (λ x, P.fold (λ s k v, s ++ "["++ to_string k ++ "↦" ++ to_string v ++"]" ) x "{" ++ "}")%string.

End lat.

End WPFun.

(** Option type. *)
Inductive toplift (A: Type) := All | Just : A → toplift A.
Notation "x +⊤" := (toplift x) (at level 39).
Notation noitpo := toplift (only parsing).
Arguments All [A].
Arguments Just [A] v.

Definition toplift_bind {A B: Type} (f: A → B+⊤) (x: A+⊤) : B+⊤ :=
  match x with
  | All => All
  | Just x' => f x'
  end.

Notation "'do' X <- A ; B" := (toplift_bind (fun X => B) A)
 (at level 200, X ident, A at level 100, B at level 200)
 : noitpo_monad_scope.

(* same kind of notation, but with a unique name *)
Notation "'do_top' X <- A ; B" := (toplift_bind (fun X => B) A)
 (at level 200, X ident, A at level 100, B at level 200).

Lemma top_bind_case A B (a: A+⊤) (f: A → B+⊤) :
  ∀ P : B+⊤ → Prop,
    P All →
    (∀ a', a = Just a' → P (f a')) →
    P (do_top x <- a; f x).
Proof.
  destruct a. exact (λ P H _, H). exact (λ P _ H, H _ eq_refl).
Qed.

Ltac destruct_noitpo_in_goal :=
  match goal with [ |- context[match ?x with Just _ => _ | All => _ end]] => destruct x end.

Ltac destruct_noitpo_in_goal_eq :=
  match goal with [ |- context[match ?x with Just _ => _ | All => _ end]] => case_eq x end.

Definition noitpo_lift {A B: Type} (f: A → B) : noitpo A → noitpo B :=
  toplift_bind (fun x => Just (f x)).

Definition noitpo_bind2 {A B C: Type} (f: A → B → noitpo C) (x: noitpo A) (y: noitpo B) : noitpo C :=
  match x, y with
  | All, _ | _, All => All
  | Just x', Just y' => f x' y'
  end.

Definition noitpo_lift2 {A B C: Type} (f: A → B → C) : noitpo A → noitpo B → noitpo C :=
  noitpo_bind2 (fun x y => Just (f x y)).

Definition noitpo_leb {A: Type} (leb: A → A → bool) (x y: noitpo A) : bool :=
  match x, y with
  | _, All => true
  | All, Just _ => false
  | Just x', Just y' => leb x' y'
  end.

Definition flat_top_leb {A} (beq: A → A → bool) (x y: A+⊤) : bool :=
  match x, y with
  | _, All => true
  | All, _ => false
  | Just x', Just y' => beq x' y'
  end.

Definition flat_top_join {A} beq (x y: A+⊤) : A +⊤ := if flat_top_leb beq x y then y else All.

Local Instance flat_top_wlat A beq : weak_lattice (A+⊤) :=
  {| leb := flat_top_leb beq
   ; top := All
   ; join := flat_top_join beq
   ; widen := flat_top_join beq
  |}.

Instance noitpo_toString A `{ToString A} : ToString (noitpo A) :=
  { to_string x := match x with
                   | All => "⊤"%string
                   | Just y => to_string y
                   end
  }.

(** Partial order with partial least upper bound. *)

Local Unset Elimination Schemes.
Record pre_lattice t :=
  { pl_leb  : t → t → bool
  ; pl_join : t → t → t+⊤
  ; pl_widen: t → t → t+⊤
  }.
Instance toplift_gamma t B (GAMMA: gamma_op t B) : gamma_op (t+⊤) B :=
  λ x, match x with All => λ _, True | Just y => γ y end.

Record pre_lattice_spec t B (PL: pre_lattice t) (GAMMA: gamma_op t B) : Prop :=
  { pl_gamma_monotone: ∀ x y : t, pl_leb PL x y = true →
                                  ∀ b : B, γ x b → γ y b
  ; pl_join_sound: ∀ x y: t, (γ x ∪ γ y) ⊆ γ (pl_join PL x y)
  }.

Instance weak_lattice_of_pre_lattice t (PL: pre_lattice t) : weak_lattice (t+⊤) :=
  let join f x y :=
      match x, y with
      | All, _
      | _, All => All
      | Just x', Just y' => f x' y'
      end in
  {| leb := flat_top_leb (pl_leb PL)
   ; top := All
   ; join := join (pl_join PL)
   ; widen:= join (pl_widen PL)
  |}.

Lemma adom_of_pre_lattice t B (PL: pre_lattice t) G (PLP: pre_lattice_spec PL G)
  : adom (t+⊤) B (weak_lattice_of_pre_lattice PL) (toplift_gamma G).
Proof.
  split.
+ intros [|a] [|b]; simpl; auto. discriminate. intros _ ? _. easy.
  apply (pl_gamma_monotone PLP).
+ easy.
+ intros [|a] [|b]; intros; try easy.
  apply pl_join_sound; auto.
Qed.

Definition flat_pre_lattice T (beq: T → T → bool ) : pre_lattice T :=
  {| pl_leb := beq
   ; pl_join x y := if beq x y then Just x else All
   ; pl_widen x y := if beq x y then Just x else All
  |}.

Lemma flat_pre_lattice_correct T B beq (BEQ: ∀ x y, beq x y = true → x = y)
      (G: gamma_op T B) : pre_lattice_spec (flat_pre_lattice beq) G.
Proof.
  split.
- intros x y H. rewrite (BEQ _ _ H). easy.
- intros x y a H. simpl. generalize (BEQ x y). destruct (beq x y). intuition. subst. easy. easy.
Qed.

Local Open Scope noitpo_monad_scope.
Definition product_pre_lattice {A B} (PA: pre_lattice A) (PB: pre_lattice B) : pre_lattice (A * B) :=
  {| pl_leb x x' := let '(a,b) := x in let '(a',b') := x' in
                    pl_leb PA a a' && pl_leb PB b b'
   ; pl_join x x'  := let '(a,b) := x in let '(a',b') := x' in
                      do α <- pl_join PA a a';
                      do β <- pl_join PB b b';
                      Just (α, β)
   ; pl_widen x x' := let '(a,b) := x in let '(a',b') := x' in
                      do α <- pl_widen PA a a';
                      do β <- pl_widen PB b b';
                      Just (α, β)
  |}.

Instance pair_gamma {A B Ca Cb} (GA: gamma_op A Ca) (GB: gamma_op B Cb) : gamma_op (A * B) (Ca * Cb) :=
  λ x x', let '(a, b) := x in let '(a', b') := x' in
          a' ∈ γ(a) ∧ b' ∈ γ(b).

Lemma product_pre_lattice_correct {A B Ca Cb} {PA: pre_lattice A} {PB: pre_lattice B} (GA: gamma_op A Ca) (GB: gamma_op B Cb) (HA: pre_lattice_spec PA GA) (HB: pre_lattice_spec PB GB) : pre_lattice_spec (product_pre_lattice PA PB) (pair_gamma GA GB).
Proof.
  split.
- intros (a,b) (a',b'). simpl. rewrite andb_true_iff.
  intros [H H'] (u,v) [K K'].
  split; eapply pl_gamma_monotone; eauto.
- intros (a,b) (a',b') (α, β).
  generalize (@pl_join_sound _ _ _ _ HB b b' β).
  generalize (@pl_join_sound _ _ _ _ HA a a' α).
  simpl.
  destruct (pl_join PA a a'). easy.
  destruct (pl_join PB b b'). easy.
  intros ? ? [(?,?)|(?,?)]; split; intuition.
Qed.

Module WPFun2 (T:TREE).
Module P := Tree_Properties T.
Section elt.

  Context (elt B: Type)
          (PL: pre_lattice elt)
          (elt_gamma: gamma_op elt B)
          (PLP: pre_lattice_spec PL elt_gamma).

  Definition t : Type := T.t elt.

  Definition get (p: T.elt) (x: t) : elt+⊤ :=
    match T.get p x with
    | Some r => Just r
    | None => All
    end.

  Definition set (x:t) (p: T.elt) (v: elt+⊤) : t :=
    match v with
    | All => T.remove p x
    | Just v' => T.set p v' x
    end.

  Lemma gsspec x p v p' :
    get p' (set x p v) = if T.elt_eq p' p then v else get p' x.
  Proof.
    unfold get.
    destruct v as [|v]; simpl.
    now rewrite T.grspec; destruct T.elt_eq.
    now rewrite T.gsspec; destruct T.elt_eq.
  Qed.

  Definition leb : t → t → bool :=
    λ x y,
    P.for_all y (λ a s, match T.get a x with
                        | Some a' => pl_leb PL a' s
                        | None => false
                        end).

  Lemma leb_le (x y: t) :
    leb x y = true <->
    ∀ p : T.elt, flat_top_leb (pl_leb PL) (get p x) (get p y) = true.
  Proof.
    unfold leb, get, flat_top_leb.
    rewrite P.for_all_correct.
    split; intros H p; specialize (H p);
    destruct (T.get p x);
    destruct (T.get p y); eauto;
    congruence.
  Qed.

  Lemma leb_refl
        (H: ∀ x, pl_leb PL x x = true)
        (x: t) : leb x x = true.
  Proof.
    apply leb_le. unfold get.
    intros p. destruct T.get; simpl; auto.
  Qed.

  Definition join f : t → t → t :=
    T.combine (λ u v, match u, v with
                      | None, _
                      | _, None => None
                      | Some u', Some v' =>
                        match f u' v' with
                        | Just r => Some r
                        | All => None
                        end
                      end).

  Lemma join_monotone f x a b :
    (∀ u v, pl_leb PL u v = true →
            (∀ w v', f v w = Just v' → pl_leb PL u v' = true)
          ∧ (∀ w v', f w v = Just v' → pl_leb PL u v' = true)) →
    leb x a = true ∨ leb x b = true →
    leb x (join f a b) = true.
  Proof.
    intros F [H|H]; rewrite leb_le in *.
    intros p. specialize (H p).
    unfold join, get in *.
    rewrite T.gcombine.
    destruct (T.get p x) as [u|].
    destruct (T.get p a) as [v|]; auto.
    destruct (T.get p b) as [w|]; auto.
    specialize (F _ _ H). destruct F as [F _]. specialize (F w).
    destruct f. auto. eauto.
    destruct (T.get p a) as [v|]; auto.
    discriminate.
    easy.
    intros p. specialize (H p).
    unfold join, get in *.
    rewrite T.gcombine.
    destruct (T.get p x) as [u|].
    destruct (T.get p a) as [v|];
    destruct (T.get p b) as [w|]; auto.
    specialize (F _ _ H). destruct F as [_ F]. specialize (F v).
    destruct f. auto. eauto.
    destruct (T.get p a) as [v|];
    destruct (T.get p b) as [w|]; auto.
    discriminate.
    easy.
  Qed.
   
  Instance wlat : weak_lattice t :=
    {| leb := leb
     ; top := T.empty _
     ; join := join (pl_join PL)
     ; widen := join (pl_widen PL)
    |}.

  Instance gamma : gamma_op t (T.elt → B) :=
    λ x y, ∀ e, y e ∈ γ (get e x).
  
  Lemma gamma_set x a b p v :
    γ x a →
    γ v (b p) →
    (∀ q, q ≠ p → a q = b q) →
    γ (set x p v) b.
  Proof.
    intros A V H c.
    rewrite gsspec. destruct T.elt_eq.
    subst; auto.
    rewrite <- H; auto.
  Qed.

  Lemma gamma_forget x a b p :
    γ x a →
    (∀ q, q ≠ p → a q = b q) →
    γ (set x p All) b.
  Proof.
    intros A H c. specialize (H c).
    rewrite gsspec. destruct T.elt_eq as [EQ|NE].
    easy.
    rewrite <- (H NE). exact (A c).
  Qed.

  Lemma adom : adom t (T.elt → B) wlat gamma.
  Proof.
    split.
    + intros x y H c X d. simpl in *. unfold leb in H. rewrite P.for_all_correct in H.
      specialize (H d). specialize (X d). unfold get in *.
      destruct (T.get d y).
      specialize (H _ eq_refl). destruct T.get. hnf. eapply pl_gamma_monotone; eauto.
      discriminate.
      easy.
    + intros x y. unfold get. rewrite T.gempty. easy.
    + intros x y a H c. simpl. unfold get, join.
      rewrite T.gcombine. 2: reflexivity.
      destruct H as [H|H]; specialize (H c); unfold get in H.
      - destruct (T.get c x) as [u|].
        * destruct (T.get c y) as [v|].
          generalize (pl_join_sound PLP u v (or_introl H)).
          destruct pl_join; eauto.
          easy.
        * easy.
      - destruct (T.get c x) as [u|].
        * destruct (T.get c y) as [v|].
          generalize (pl_join_sound PLP u v (or_intror H)).
          destruct pl_join. eauto.
          eauto.
          easy.
        * easy.
  Qed.
  
  Instance toString `{ToString T.elt} `{ToString elt} : ToString (T.t elt) :=
    (λ x, T.fold (λ s k v, s ++ "["++ to_string k ++ "↦" ++ to_string v ++"]" ) x "{" ++ "}")%string.

End elt.

  Opaque get. (* TODO *)
  Opaque set. (* TODO *)

End WPFun2.
