Require Import
  Coqlib Utf8
  Relations
  Integers
  LatticeSignatures
  AbMachineNonrel
  Goto.

Require CompleteLattice.

Unset Elimination Schemes.

Ltac vauto :=
  (econstructor (first [ now eauto | econstructor (now eauto) ])) || idtac.

(* Flag *)
Definition flag_state := flag → bool.
Definition eval_flag (i j: int) (f: flag) : bool :=
  match f with
  | FLE => negb (Int.lt j i)
  | FLT => Int.lt i j
  | FEQ => Int.eq i j
  end.
Definition compare := eval_flag.

(* Registers *)
Definition register_state := register → int.

Notation "R # r ← v" := (upd R r v) (at level 60, r at next level).

(* Memory *)
Definition memory := int → int.

(* Machine configuration *)
Record machine_config := {
  pc : int;
  mc_flg : flag_state;
  mc_reg : register_state;
  mc_mem : memory
}.

(* Execution state *)
Inductive machine_state :=
 | Halted (v:int)
 | Running (c:machine_config)
.

Notation "⌈ v ⌉" := (Halted v) (at level 2).
Notation "⟨ pp , f , r , m ⟩" := (Running {| pc := pp; mc_flg:= f; mc_reg:= r; mc_mem := m |}) (at level 2).
Notation "⌊ x ⌋" := (Some x).

Lemma run_not_hlt {pp f r m v} :
  ⟨ pp, f, r, m ⟩ = ⌈v⌉ → ∀ P : Prop, P.
Proof. exact (λ H, match H in _ = x return if x then _ else True with eq_refl => I end). Qed.

Lemma run_inv {pp f r m pp' f' r' m'} :
  ⟨ pp, f, r, m ⟩ = ⟨ pp', f', r', m' ⟩ →
  ∀ P : _ → _ → _ → _ → Prop,
    P pp f r m →
    P pp' f' r' m'.
Proof.
  intros H.
  set (d ms :=
         match ms with
         | ⟨ i, j, k, l ⟩ => ∀ P : _ → _ → _ → _ → Prop, P pp f r m → P i j k l
         | _ => ∀ P : _ → _ → _ → _ → Prop, P pp f r m → P pp' f' r' m'
         end).
  change (d ⟨ pp', f', r', m' ⟩).
  destruct H. exact (λ _, id).
Qed.

Reserved Notation "a =~> b" (at level 70).

Coercion Z.of_nat : nat >-> Z.
Notation "p + q" := (Int.add p (Int.repr q)) (left associativity, at level 50) : goto_scope.
Notation "x [ op ] y" := (eval_int_binop op x y) (at level 80) : goto_scope.
Notation "'dec'" := (decode_from) (only parsing) : goto_scope.

Local Open Scope goto_scope.

Inductive small_step : relation machine_state :=
| SCst pp f r m v rd z : dec m pp = ⌊(ICst v rd, z)⌋ →
  ⟨ pp, f, r, m ⟩ =~> ⟨ pp+z, f, r#rd ← v, m ⟩
| SCmp pp f r m rs rd z : dec m pp = ⌊(ICmp rs rd, z)⌋ →
  ⟨ pp, f, r, m ⟩ =~> ⟨ pp+z, compare (r rd) (r rs), r, m ⟩
| SBinop pp f r m op rs rd z : dec m pp = ⌊(IBinop op rs rd, z)⌋ →
  ⟨ pp, f, r, m ⟩ =~> ⟨ pp+z, f, r#rd ← (r rs [op] r rd), m ⟩
| SLoad pp f r m rs rd z : dec m pp = ⌊(ILoad rs rd, z)⌋ →
  ⟨ pp, f, r, m ⟩ =~> ⟨ pp+z, f, r#rd ← m (r rs), m ⟩
| SStore pp f r m rs rd z : dec m pp = ⌊(IStore rs rd, z)⌋ →
  ⟨ pp, f, r, m ⟩ =~> ⟨ pp+z, f, r, m # r rd ← r rs ⟩
| SGoto pp f r m v z : dec m pp = ⌊(IGoto v, z)⌋ →
  ⟨ pp, f, r, m ⟩ =~> ⟨ v, f, r, m ⟩
| SGotoCond pp f r m c v z : dec m pp = ⌊(IGotoCond c v, z)⌋ →
  ⟨ pp, f, r, m ⟩ =~> ⟨ if f(c) then v else pp+z, f, r, m ⟩
| SGotoInd pp f r m rd z : dec m pp = ⌊(IGotoInd rd, z)⌋ →
  ⟨ pp, f, r, m ⟩ =~> ⟨ r(rd), f, r, m ⟩
| SSkip pp f r m z : dec m pp = ⌊(ISkip, z)⌋ →
  ⟨ pp, f, r, m ⟩ =~> ⟨ pp+z, f, r, m ⟩
| SHalt pp f r m rd z : dec m pp = ⌊(IHalt rd, z)⌋ →
  ⟨ pp, f, r, m ⟩ =~> ⌈r rd⌉
where "a =~> b" := (small_step a b).

(* Some small inversion principles. *)
Lemma small_step_hlt_inv_P msi res (P: machine_state → int → Prop) :
  msi =~> ⌈res⌉ →
  (∀ pc f r m, ∀ rd z,
     ⟨ pc, f, r, m ⟩ =~> ⌈r rd⌉ →
     decode_from m pc = ⌊(IHalt rd, z)⌋ →
     P ⟨ pc, f, r, m ⟩ (r rd)
  ) →
  P msi res.
Proof.
  intros H.
  set (d ms r := match r with
              | ⌈res⌉ =>
                (∀ pc f r m, ∀ rd z,
                   ⟨ pc, f, r, m ⟩ =~> ⌈r rd⌉ →
                   decode_from m pc = ⌊(IHalt rd, z)⌋ →
                   P ⟨ pc, f, r, m ⟩ (r rd)
                ) → P ms res
              | _ => msi =~> ⌈res⌉
              end).
  change (d msi ⌈res⌉).
  case H; auto.
  simpl. intros pp f r m rd z HI H0. eapply H0; auto. vauto. eauto.
Qed.

(* Weaker form simpler to use. *)
Corollary small_step_hlt_inv msi res :
  msi =~> ⌈res⌉ →
  ∃ pc f r m rd z, msi = ⟨pc, f, r, m⟩ ∧ res = r rd ∧ decode_from m pc = ⌊(IHalt rd, z)⌋.
Proof.
  intros K.
  apply (small_step_hlt_inv_P msi res). exact K.
  intros. repeat eexists.
  eauto.
Qed.

Definition initial_state f r m : machine_state :=
  ⟨ Int.zero, f, r, m  ⟩.

Definition sos_star := clos_refl_trans _ small_step.
Notation "a ⇉★ b" := (sos_star a b) (at level 70).

Definition reachable I (s: machine_state) : Prop :=
  ∃ f r, initial_state f r I ⇉★ s.

Lemma reachable_step I s :
  reachable I s →
  ∀ s', s =~> s' →
  reachable I s'.
Proof.
  intros (f & r & H) s' S.
  exists f, r. vauto.
Qed.

(** The machine is stuck if it is not halted yet cannot make progress. *)
Definition stuck (s: machine_state) : Prop :=
  match s with
  | ⌈_⌉ => False
  | ⟨_, _, _, _⟩ => ∀ s', ¬ s =~> s'
  end.

(** Here, being stuck means that the instruction at current program point
    cannot be decoded. *)
Lemma stuck_is_decode_failure s :
  stuck s ↔ match s with ⟨ pp, f, r, m ⟩ => decode_from m pp = None | _ => False end.
Proof.
  destruct s as [v|[pp f r m]]. easy.
  case_eq (decode_from m pp). intros (i, z) Hi.
  split. 2: discriminate.
  destruct i; intros STUCK; apply False_ind;
  try now eapply (STUCK); vauto.
  intros K. split. auto. intros _.
  intros s' S.
  inversion S; congruence.
Qed.

Lemma small_step_dec s :
  {∃ v, s = ⌈v⌉ } + { ∃ s', s =~> s' } + { stuck s }.
  refine (
  match s with
  | ⌈v⌉ => inleft (left (ex_intro _ v eq_refl))
  | ⟨ pp, f, r, m ⟩ =>
    match decode_from m pp as x return _ = x → _ with
    | ⌊i⌋ => λ N, inleft (right _)
    | None => λ N, inright _
    end eq_refl
  end
  ).
Proof.
  abstract (destruct i as (i, z); destruct i; vauto).
  abstract (rewrite stuck_is_decode_failure; exact N).
Defined.

Lemma not_stuck s :
  ¬ stuck s →
  (∃ v, s = ⌈v⌉) ∨ (∃ s', s =~> s').
Proof.
  generalize (small_step_dec s). intuition.
Qed.

(** A program is safe if it cannot reach a state in which it is stuck. *)
Definition safe P : Prop :=
  ∀ s, reachable P s → ¬ stuck s.

Notation Env := (machine_state → Prop).

Definition initial_env (I: memory) : Env := λ ms,
match ms with
| ⟨ z, _, _, m ⟩ => z = Int.zero ∧ m = I
| ⌈_⌉ => False
end.

Definition post : Env → Env := fun E msi =>
  ∃ msi', E msi' ∧ msi' =~> msi.

Definition semantics_fun (I: memory) : Env → Env :=
  λ e, initial_env I ∪ post e.

Instance semantics_fun_mon (I:memory) : CompleteLattice.monotone Env Env (semantics_fun I).
Proof.
  firstorder.
Qed.

Definition semantics prg : Env := CompleteLattice.lfp (semantics_fun_mon prg).

Notation "⟦ c ⟧" := (semantics c) (at level 2).

Definition reachable_env (I: memory) : Env :=
  fun s =>
    ∃ i, initial_env I i
       ∧ clos_refl_trans _ small_step i s.

Lemma reachable_in_sem (prg:memory) :
  reachable prg ⊆ ⟦ prg ⟧.
Proof.
  intros m (f & r & Hr).
  apply (clos_refl_trans_ind_left _ small_step (initial_state f r prg) ⟦prg ⟧); auto.
+ (* Initial (reflexive) case *)
  apply (CompleteLattice.lfp_fixpoint _ _ _ (semantics_fun_mon prg)). vauto.
+ (* Transitive case *)
  intros mi m2 ?. intros Hi Hs.
  apply (CompleteLattice.lfp_fixpoint _ _ _ (semantics_fun_mon prg)).
  firstorder.
Qed.

Lemma sem_in_reachable (prg: memory) :
  ⟦prg⟧ ⊆ reachable(prg).
Proof.
  refine (CompleteLattice.lfp_least_postfixpoint _ _ _ (semantics_fun_mon prg) _ _).
  unfold semantics_fun.
  intros [q|[pp f r m]].
+ (* Halt *)
  intros [()|([|[pp f r m]] & H & S)].
  destruct (small_step_hlt_inv _ _ S)
    as (pp & f & r & m & rd & z & K & _). discriminate.
  eapply reachable_step; eauto.
+ (* Run *)
  intros [(-> & ->)|(msi & H & S)].
  exists f, r. vauto.
  eapply reachable_step; eauto.
Qed.

Definition upd_mem : memory → addr → int → memory := upd.
Definition encode_program (prg: list instruction) (m:memory) : memory * list int :=
  @List.fold_left
    (memory * list int) instruction
    (λ m_n i,
     let v := encode_instr i in
     @List.fold_left
       (memory * list int) int
       (λ m_n j,
        let (m, n) := m_n in
        let (pp, ppl) := match n with hd::tl => (Int.add hd Int.one, n) | nil => (Int.zero, nil) end in
        (upd_mem m pp j, pp::ppl))
       v
       m_n)
    prg
    (m, nil).
