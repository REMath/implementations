Require Import
  Coqlib Utf8 Util Relations
  Integers
  Goto GotoSem.

Unset Elimination Schemes.

Open Scope goto_scope.

Definition step (mc: machine_config) : option machine_state :=
  let (p, f, r, m) := mc in
  match decode_from m p with
  | ⌊(ICst v rd, z)⌋ => Some ⟨ p+z, f, r#rd ← v, m ⟩
  | ⌊(ICmp rs rd, z)⌋ => Some ⟨ p+z, compare (r rd) (r rs), r, m ⟩
  | ⌊(IBinop op rs rd, z)⌋ => Some ⟨ p+z, f, r#rd ← (r rs [op] r rd), m ⟩
  | ⌊(ILoad rs rd, z)⌋ => Some ⟨ p+z, f, r#rd ← m (r rs), m ⟩
  | ⌊(IStore rs rd, z)⌋ => Some ⟨ p+z, f, r, m # r rd ← r rs ⟩
  | ⌊(IGoto v, z)⌋ => Some ⟨ v, f, r, m ⟩
  | ⌊(IGotoCond c v, z)⌋ => Some ⟨ if f(c) then v else p+z, f, r, m ⟩
  | ⌊(IGotoInd rd, z)⌋ => Some ⟨ r(rd), f, r, m ⟩
  | ⌊(ISkip, z)⌋ => Some ⟨ p+z, f, r, m ⟩
  | ⌊(IHalt rd, z)⌋ => Some ⌈r rd⌉
  | None => None
  end.

Lemma step_sound mc ms :
  step(mc) = ⌊ms⌋ ↔ Running mc =~> ms.
Proof.
  destruct mc as (p, f, r, m).
  unfold step.
  split.
+ destruct (decode_from m p) as [(i,z)|] eqn: DEC.
  destruct i; intro; eq_some_inv; subst; vauto.
  intro; eq_some_inv.
+ intros H; inversion H;
  match goal with H : decode_from _ _ = _ |- _ => rewrite H end;
  reflexivity.
Qed.

Inductive answer := Ans (v: int) | Wrong | TimeOut (mc: machine_config).

Fixpoint steps (mc: machine_config) (fuel: nat) {struct fuel} : answer :=
  match fuel with
  | S fuel' =>
    match step mc with
    | ⌊Running mc'⌋ => steps mc' fuel'
    | ⌊⌈v⌉⌋ => Ans v
    | None => Wrong
    end
  | O => TimeOut mc
  end.

Lemma steps_timeout_reachable mc' fuel :
  ∀ mc, steps mc fuel = TimeOut mc' →
        sos_star (Running mc) (Running mc').
Proof.
  induction fuel; intros mc H; inversion H.
  apply rt_refl.
  clear H.
  destruct (step mc) as [[v|m']|] eqn: STEP. discriminate. 2: discriminate.
  apply step_sound in STEP.
  specialize (IHfuel _ H1).
  vauto.
Qed.

Lemma last_step fuel :
  ∀ mc a,
  steps mc (S fuel) = a →
  ∃ mc' fuel',
    steps mc fuel' = TimeOut mc' ∧ steps mc' (S O) = a.
Proof.
  induction fuel as [|fuel IH].
  intros mc a <-. exists mc, O. auto.
  intros mc a. simpl.
  destruct (step mc) as [[v|m]|] eqn: STEP.
  intros <-. exists mc, O. split. reflexivity. rewrite STEP. auto.
  intros H. destruct (IH _ _ H) as (m' & fuel' & K & L).
  eexists. exists (S fuel'). split. 2: exact L.
  simpl. rewrite STEP. exact K.
  intros <-. eexists _, O. split. reflexivity. rewrite STEP. reflexivity.
Qed.

Definition run (P: memory) (fuel: nat) : answer :=
  steps {| pc := Int.zero ; mc_flg := λ _, false ; mc_reg := λ _, Int.zero ; mc_mem := P |} fuel.

Theorem safe_programs_do_not_go_wrong P :
  safe P →
  ∀ fuel, run P fuel ≠ Wrong.
Proof.
  intros SAFE fuel.
  unfold run.
  destruct fuel as [|fuel]. discriminate.
  intros H. destruct (last_step _ _ _ H) as (mc & fuel' & K & L).
  apply steps_timeout_reachable in K.
  refine (SAFE (Running mc) _ _). vauto.
  destruct mc as [p f r m].
  intros s' Q. apply step_sound in Q. unfold steps in L. rewrite Q in L.
  destruct s'; discriminate.
Qed.
