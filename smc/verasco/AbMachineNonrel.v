Require Import
  Coqlib Utf8
  Integers DLib
  LatticeSignatures
  IntSet
  IntervalDomain AdomLib.

Set Implicit Arguments.

(** Numerical operations available on numerical domains. *)
Inductive int_unary_operation :=
| OpNeg | OpNot.

Inductive int_binary_operation :=
| OpAdd | OpSub | OpMul | OpDivs | OpShl | OpShr | OpShru
| OpAnd | OpOr  | OpXor
| OpCmp (c: comparison) | OpCmpu (c: comparison).

Definition eval_int_unop op : int → int :=
  match op with
  | OpNeg => Int.neg
  | OpNot => Int.not
  end.

Definition eval_int_binop op : int → int → int :=
  match op with
  | OpAdd => Int.add
  | OpSub => Int.sub
  | OpMul => Int.mul
  | OpDivs => Int.divs
  | OpShl => Int.shl
  | OpShr => Int.shr
  | OpShru => Int.shru
  | OpAnd => Int.and
  | OpOr => Int.or
  | OpXor => Int.xor
  | OpCmp c => fun x y => Interval.of_bool (Int.cmp c x y)
  | OpCmpu c => fun x y => Interval.of_bool (Int.cmpu c x y)
  end.

(** Specifications of the numerical operations on sets of concrete values. *)
Definition lift_unop {T U:Type} (op: T → U) (A: ℘ T) : ℘ U :=
  fun i => ∃ j, A j ∧ i = (op j).

Definition Eval_int_unop (op: int_unary_operation) : ℘ int → ℘ int :=
  lift_unop (eval_int_unop op).

Definition lift_binop {T U:Type} (op: T → T → U) (A B: ℘ T) : ℘ U :=
  fun i => ∃ a, ∃ b, A a ∧ B b ∧ i = (op a b).

Definition Eval_int_binop (op: int_binary_operation) : ℘ int → ℘ int → ℘ int :=
  lift_binop (eval_int_binop op).

(** Signature of an abstract non relationnal numerical domain on machine numbers. *)
Unset Elimination Schemes.
Class ab_machine_int (t_int:Type) : Type :=
{ as_int_wl :> weak_lattice t_int
; as_int_gamma :> gamma_op t_int int
; as_int_adom :> adom t_int int as_int_wl as_int_gamma

; size: t_int → noitpo N
; concretize: t_int → fint_set

; meet_int: t_int → t_int → t_int+⊥

; const_int: int → t_int
; booleans: t_int
; range_int: t_int → signedness → Interval.itv+⊥

; forward_int_unop: int_unary_operation → t_int → t_int+⊥
; forward_int_binop: int_binary_operation → t_int → t_int → t_int+⊥

; is_in_itv: int → int → t_int → bool

; backward_int_unop: int_unary_operation → t_int → t_int → t_int+⊥
; backward_int_binop: int_binary_operation → t_int → t_int → t_int → t_int+⊥ * t_int+⊥
}.

(** Specification of an abstract numerical domain. *)
Class ab_machine_int_correct t_int (D: ab_machine_int t_int) : Prop :=
{ meet_int_correct: ∀ (x:t_int) y, (γ x) ∩ (γ y) ⊆ γ (meet_int x y)
; concretize_correct: ∀ (x:t_int), γ x ⊆ γ (concretize x)
; const_int_correct: ∀ n: int, γ (const_int n:t_int) n
; booleans_correct0: γ (booleans:t_int) Int.zero
; booleans_correct1: γ (booleans:t_int) Int.one
; range_int_correct: ∀ x:t_int, γ x ⊆ ints_in_range (range_int x)
; forward_int_unop_sound: ∀ op (x:t_int), Eval_int_unop op (γ x) ⊆ γ (forward_int_unop op x)
; forward_int_binop_sound: ∀ op (x y:t_int), Eval_int_binop op (γ x) (γ y) ⊆ γ (forward_int_binop op x y)

; is_in_itv_correct (m M:int) : ∀ x: t_int, is_in_itv m M x = true →
    ∀ i, γ x i → Int.lt M i = false ∧ Int.lt i m = false

; backward_int_unop_sound:
    ∀ op (x y:t_int) i, γ x i → γ y (eval_int_unop op i) → γ (backward_int_unop op x y) i
; backward_int_binop_sound: ∀ op (x y:t_int) z, ∀ i j : int,
    γ x i → γ y j → γ z (eval_int_binop op i j) →
    let '(u,v) := backward_int_binop op x y z in
    γ u i ∧ γ v j
}.

Class reduction A B : Type := ρ: A+⊥ → B+⊥ → (A * B)+⊥.
Definition reduction_correct A B t WLA GA (Ha:adom A t WLA GA) WLB GB (Hb:adom B t WLB GB) `{reduction A B} : Prop :=
  ∀ (a : A+⊥) (b : B+⊥),
    γ a ∩ γ b ⊆
    match ρ a b with
      | Bot => ∅
      | NotBot (u,v) => γ u ∩ γ v
    end.

(** Reduced product of two abstract numerical domains. *)
Definition red_prod_unop {A B C D} ρ (opa: A → B+⊥) (opb: C → D+⊥) : A*C → (B*D)+⊥ :=
  fun x => match x with (a,b) => ρ (opa a) (opb b) end.

Definition red_prod_binop {A B C D} ρ (opa: A → A → B+⊥) (opb: C → C → D+⊥)
  : (A*C) → (A*C) → (B*D)+⊥ :=
  fun x y => match x,y with (a,b), (c,d) =>
                            ρ (opa a c) (opb b d)
             end.

Definition red_prod_backop_un {A B C D} ρ (opa: A → B → A+⊥) (opb: C → D → C+⊥)
  : (A*C) → (B*D) → (A*C)+⊥ :=
  fun x y => match x,y with
               | (a,b), (c,d) =>
                 let a' := opa a c in
                 let b' := opb b d in
                 (ρ a' b')
             end.

Definition red_prod_backop_bin {A B C D} ρ (opa: A → A → B → A+⊥ * A+⊥) (opb: C → C → D → C+⊥ * C+⊥)
  : (A*C) → (A*C) → (B*D) → (A*C)+⊥ * (A*C)+⊥ :=
  fun x y z => match x,y,z with
               | (a,b), (c,d), (e,f) =>
                 let '(a',c') := opa a c e in
                 let '(b',d') := opb b d f in
                 (ρ a' b', ρ c' d')
             end.

Instance reduced_product_int A_int B_int {Da:ab_machine_int A_int} {Db:ab_machine_int B_int}
         (Ρ_int: reduction A_int B_int)
  : ab_machine_int (A_int*B_int) :=
{| as_int_wl := WProd.make_wl as_int_wl as_int_wl
 ; as_int_gamma := WProd.gamma as_int_gamma as_int_gamma
 ; as_int_adom := WProd.make as_int_adom as_int_adom
 ; size x := match size (fst x), size (snd x) with All, a | a, All => a | Just a, Just b => Just (N.min a b) end
 ; concretize x := match fs_meet (concretize (fst x)) (concretize (snd x)) with NotBot m => m | Bot => fempty end
 ; meet_int x y := ρ (meet_int (fst x) (fst y)) (meet_int (snd x) (snd y))
 ; const_int n := (const_int n, const_int n)
 ; booleans := (booleans, booleans)
 ; range_int x s := Interval.meet' (range_int (fst x) s) (range_int (snd x) s)
 ; forward_int_unop op := red_prod_unop ρ (forward_int_unop op) (forward_int_unop op)
 ; forward_int_binop op :=   red_prod_binop ρ (forward_int_binop op) (forward_int_binop op)

 ; is_in_itv m M x := let '(a,b) := x in is_in_itv m M a || is_in_itv m M b

 ; backward_int_unop op := red_prod_backop_un ρ (backward_int_unop op) (backward_int_unop op)
 ; backward_int_binop op := red_prod_backop_bin ρ (backward_int_binop op) (backward_int_binop op)
|}.

(** This reducted product yields a correct abstract numerical domain. *)
Lemma reduced_product_int_correct A_int B_int
         `{Da:ab_machine_int A_int} `{Db:ab_machine_int B_int}
         (Das: ab_machine_int_correct Da) (Dbs: ab_machine_int_correct Db)
         (Ρ_int: reduction A_int B_int) (Ρs_int: reduction_correct (@as_int_adom _ Da) (@as_int_adom _ Db))
  : ab_machine_int_correct (reduced_product_int A_int B_int Ρ_int).
Proof.
split.
- intros (a,b) (c,d). intros i [(L&R) (L'&R')]. apply Ρs_int.
  intuition auto using @meet_int_correct.
- intros (a,b) i (Ha,Hb). simpl in *.
  generalize (fs_meet_sound (concretize a) (concretize b) i (conj (concretize_correct _ _ Ha) (concretize_correct _ _ Hb))).
  simpl. destruct fs_meet; intuition.
- simpl. intros; split; apply const_int_correct.
- split; eapply booleans_correct0.
- split; eapply booleans_correct1.
- intros (a,b) i (L&R). unfold ints_in_range. split.
  apply Interval.meet'_correct; apply range_int_correct; auto.
  exploit (@range_int_correct A_int _). eapply L. unfold ints_in_range. intros [_ A].
  exploit (@range_int_correct B_int _). eapply R. unfold ints_in_range. intros [_ B].
  simpl. unfold Interval.meet'.
  destruct (range_int a Unsigned); intuition.
  destruct (range_int b Unsigned); intuition.
  simpl.
  apply Interval.meet_correctu. auto.
- intros op (a,b) i (j & (R&L) & ->). simpl. apply Ρs_int; split; apply forward_int_unop_sound; eexists; split; eauto.
- intros op (a,b) (c,d) i (j & k & (?&?) & (?&?) &->). simpl.
  apply Ρs_int; split; apply forward_int_binop_sound; eexists; eexists; intuition; eauto.
- intros m M (a,b). simpl. rewrite orb_true_iff.
  destruct 1;intros i (U&V).
  eapply (@is_in_itv_correct A_int); eauto.
  apply is_in_itv_correct with b; eauto.
- intros op(a,b)(c,d) i (?&?)(?&?). simpl; apply Ρs_int; split; apply backward_int_unop_sound; auto.
- intros op.
  intros (a,b)(c,d)(e,f) i j (?&?)(?&?)(?&?).
  pairs. simpl. pairs. intros L R ?. inj.
  generalize (backward_int_binop_sound op a c e i j).
  generalize (backward_int_binop_sound op b d f i j).
  autorw'.
  split; apply Ρs_int; intuition.
Qed.
