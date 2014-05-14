Require Import
  Coqlib Utf8 String
  Integers TreeAl Util
  Goto GotoSem AbGoto
  LatticeSignatures AdomLib
  AbMachineNonrel.
Require
  DebugAbMachineNonrel
  Containers.Maps
  CompleteLattice.

Set Implicit Arguments.
Unset Elimination Schemes.

Section ONMAPS.

  Import Containers.Maps.

  Context {A B: Type} `{OT:OrderedType A}.

  Definition map_any_fun (m: Map [ A, B ]) : option (A * B) :=
      fold (fun k v _ => Some (k,v)) m None.

  Lemma map_any_fun_spec (m: Map [A, B]) :
    match map_any_fun m with
    | Some kv => MapsTo (fst kv) (snd kv) m
    | None => Empty m
    end.
  Proof.
    unfold map_any_fun.
    apply MF.fold_rec_bis.
    intros m0 m' [(k,v)|] H H0. rewrite <- H. auto.
    generalize (MF.Empty_m H). intuition.
    apply is_empty_2. reflexivity.
    intros k e [(k',v)|] m' H H0 H1; apply add_1; auto.
  Qed.

  Definition map_any (m: Map [A, B]) : { kv : A * B | MapsTo (fst kv) (snd kv) m } + { Empty m } :=
    match map_any_fun m as res return match res with
                                      | Some kv => MapsTo (fst kv) (snd kv) m
                                      | None => Empty m end → _ with
    | Some kv => fun H => inleft (exist _ kv H)
    | None => inright
    end (map_any_fun_spec m).

End ONMAPS.

Section GOTOANALYSIS.

Variables t d: Type.
Variables (D: ab_machine_int d) (T: mem_dom t d).
Hypothesis D_correct : ab_machine_int_correct D.

Inductive ab_post_res :=
| Run (pp:addr) (m:t)
| Hlt (res: d)
| GiveUp.

Definition abstract_op (op: int_binary_operation) (m: t) (rs rd: register) : t+⊥ :=
  do_bot v <- forward_int_binop (ab_machine_int := D) op (var T m rs) (var T m rd);
  NotBot (assign T m rd v).

Let abstract_cond (f: flag) (m: t) : t+⊥ := assume T m f true.
Let abstract_ncond (f: flag) (m: t) : t+⊥ := assume T m f false.

Variable max_deref: N.

Definition concretize_with_care (v:d) : IntSet.fint_set :=
  match size v with
  | Just sz =>
    if N.leb sz max_deref
    then concretize v
    else All
  | All => All
  end.

Lemma concretize_with_care_two_cases (v:d) :
  concretize_with_care v = All
∨ ∃ l, concretize_with_care v = Just l ∧ concretize v = Just l.
Proof.
  unfold concretize_with_care.
  destruct size. auto.
  DLib.bif; auto.
  destruct (concretize); auto.
  right. eexists; eauto.
Qed.

Definition load_many_aux (m: t) (addr_set: IntSet.int_set) : d+⊥ :=
  IntSet.fold (λ acc addr, acc ⊔ NotBot (T.(load_single) m addr)) addr_set Bot.

Lemma load_many_aux_sound (m: t) (addr_set: IntSet.int_set) :
  ∀ a: int,
    a ∈ γ (Just addr_set) →
    γ (NotBot (T.(load_single) m a)) ⊆ γ (load_many_aux m addr_set).
Proof.
  Hint Resolve as_int_adom.
  unfold load_many_aux, γ, IntSet.fold.
  apply IntSet.P.fold_rec.
  simpl. intros m0 m' a H H0 a0 H1 x H2. rewrite <- H in H1. eapply H0; eauto.
  simpl. intro. rewrite ZTree.gempty. discriminate.
  simpl.
  intros m0 a k v H H0 H1 a0 H2 x H3.
  rewrite ZTree.gsspec in H2. destruct ZTree.elt_eq. clear H2.
  assert (Int.repr k = a0) as K. rewrite <- Int.repr_unsigned. f_equal. auto.
  rewrite K.
  destruct a; auto. apply join_sound; auto.
  destruct a. elim (H1 _ H2 _ H3).
  apply join_sound; auto. left. eapply H1; eauto.
Qed.

Definition load_many (m: t) (a: d) : d+⊥ :=
  match concretize_with_care a with
  | Just addr_set => load_many_aux m addr_set
  | All => NotBot top
  end.

Local Instance T_as_wl : weak_lattice t := T.(as_wl).

Definition store_many (m: t) (a: d) (v: d) : t :=
  match concretize_with_care a with
  | Just addr_set =>
    union_list_map (λ a : addr, T.(store_single) m a v) m join (IntSet.as_list addr_set)
  | All => top
  end.

Definition abstract_goto_ind (m: t) (v: d) : list ab_post_res :=
  match concretize_with_care v with
  | Just tgt =>
    IntSet.fold
      (λ acc addr,
       Run addr m :: acc (* TODO: precision loss, should assume *)
      ) tgt nil
  | All => GiveUp :: nil
  end.

Lemma abstract_goto_ind_sound m v :
  abstract_goto_ind m v = GiveUp :: nil
∨ (∀ x,
     x ∈ γ(v) → In (Run x m) (abstract_goto_ind m v)).
Proof.
  unfold abstract_goto_ind, IntSet.fold.
  destruct (concretize_with_care_two_cases v) as
      [-> | (tgt & -> & TGT)].
  left; reflexivity.
  right.
  intros x X.
  generalize (concretize_correct v x X). rewrite TGT. clear TGT.
  apply (IntSet.P.fold_rec).
  + intros m0 m' a H H0 H1. apply H0.
    unfold γ. simpl. rewrite H. exact H1.
  + unfold γ. simpl. rewrite ZTree.gempty. intros; eq_some_inv.
  + intros m0 a k v0 H H0 H1.
    unfold γ. simpl.
    rewrite ZTree.gsspec. destruct ZTree.elt_eq.
    intros _. left. subst. rewrite Int.repr_unsigned. reflexivity.
    intros K. right. auto.
Qed.

Definition bot_cons {A B: Type} (a: botlift A) (f: A → B) (l: list B) : list B :=
  match a with
  | NotBot a' => f a' :: l
  | Bot => l
  end.

Lemma In_bot_cons_right {A B} (a: A+⊥) (f: A → B) (l: list B) :
  ∀ b, In b l → In b (bot_cons a f l).
Proof.
  unfold bot_cons. destruct a; simpl; auto.
Qed.

Lemma bot_cons_nil_r {A B} (a: A+⊥) (f: A → B) (l: list B) :
  bot_cons a f l = nil → l = nil.
Proof.
  destruct a. exact id. simpl; intros; eq_some_inv.
Qed.

Local Open Scope goto_scope.

Definition abstract_goto_cond (f: flag) (m: t) (pp: int) (tgt: d): list ab_post_res :=
  match concretize_with_care tgt with
  | Just tgt =>
    bot_cons (abstract_ncond f m) (Run (pp + 2))
      (IntSet.fold
         (λ acc addr,
          bot_cons (abstract_cond f (assume_mem T m (pp+1) addr))
                   (Run addr)
                   acc
         ) tgt nil
      )
  | All => GiveUp :: nil
  end.

Lemma abstract_goto_cond_sound f m pp tgt :
  abstract_goto_cond f m pp tgt = GiveUp :: nil
∨ ((∀ v, v ∈ γ(tgt) →
         match abstract_cond f (assume_mem T m (pp+1) v) with
         | Bot => True
         | NotBot m' => In (Run v m')
                           (abstract_goto_cond f m pp tgt)
         end
   )
     ∧ match abstract_ncond f m with
       | Bot => True
       | NotBot m' => In (Run (pp + 2) m')
                         (abstract_goto_cond f m pp tgt)
       end).
Proof.
  unfold abstract_goto_cond, IntSet.fold.
  destruct (concretize_with_care_two_cases tgt)
    as [ -> | (tgt' & -> & TGT) ].
  left; reflexivity.
  right.
  split.
- intros v V.
  generalize (concretize_correct tgt v V). rewrite TGT. clear TGT.
  apply (IntSet.P.fold_rec).
  + intros m0 m' a H H0 H1. apply H0. red. simpl. rewrite H. auto.
  + intros H. red in H. simpl in H. rewrite ZTree.gempty in H.
    eq_some_inv.
  + intros m0 a k v0 H H0 H1 H2.
    destruct (abstract_cond f (assume_mem T m (pp+1) v)) as [|m'] eqn: AC. exact I.
    red in H2. simpl in H2. rewrite ZTree.gsspec in H2.
    destruct ZTree.elt_eq.
    * clear H2. subst.
      rewrite Int.repr_unsigned, AC.
      apply In_bot_cons_right. left; reflexivity.
    * specialize (H1 H2).
      destruct abstract_ncond; simpl in *.
      apply In_bot_cons_right. exact H1.
      destruct H1 as [H1|H1]. left; exact H1.
      right. apply In_bot_cons_right. exact H1.
- destruct abstract_ncond. exact I.
  left; reflexivity.
Qed.

Inductive ab_instruction :=
(** arithmetic *)
| AICst (v:d) (dst:register)
| AIBinop (op: int_binary_operation) (src dst: register)
| AICmp (src dst: register)
(** memory *)
| AILoad  (src dst: register)
| AIStore (src dst: register)
(** control *)
| AIGoto (tgt: d)
| AIGotoCond (f: flag)  (tgt: d)
| AIGotoInd (r: register)
| AISkip
| AIHalt (r: register)
.

Definition abstract_decode_instr_at (m: t) (base: int) (i: int) : option (ab_instruction * nat) :=
  match split_instruction i with
  | (0, 0, src, 0) => do_opt rs <- decode_register src; Some (AIHalt rs, 1%nat)
  | (1, 0, 0, 0) => Some (AISkip, 1%nat)
  | (2, 0, src, 0) => do_opt rs <- decode_register src; Some (AIGotoInd rs, 1%nat)
  | (3, flg, 0, 0) =>
    do_opt f <- decode_flag flg;
    Some (AIGotoCond f (T.(load_single) m (base+1)), 2%nat)
  | (4, 0, 0, 0) => Some (AIGoto (T.(load_single) m (base+1)), 2%nat)
  | (5, 0, src, dst) => do_opt rs <- decode_register src;
                        do_opt rd <- decode_register dst;
                        Some (AIStore rs rd, 1%nat)
  | (6, 0, src, dst) => do_opt rs <- decode_register src;
                        do_opt rd <- decode_register dst;
                        Some (AILoad rs rd, 1%nat)
  | (7, 0, src, dst) => do_opt rs <- decode_register src;
                        do_opt rd <- decode_register dst;
                        Some (AICmp rs rd, 1%nat)
  | (8, o, src, dst) => do_opt op <- decode_binop o;
                        do_opt rs <- decode_register src;
                        do_opt rd <- decode_register dst;
                        Some (AIBinop op rs rd, 1%nat)
  | (9, 0, 0, dst) => do_opt rd <- decode_register dst;
                      Some (AICst (T.(load_single) m (base+1)) rd, 2%nat)
  | _ => None
  end.

Definition abstract_decode_at (pp:int) (ab:t) : (list (ab_instruction * nat))+⊤ :=
  do_top instr <- concretize_with_care (T.(load_single) ab pp);
  Just (IntSet.fold (λ acc inst,
               match abstract_decode_instr_at
                              ab (* precision loss *)
                              pp
                              inst with
               | Some i => i :: acc
               | None => acc
               end)
              instr nil).

Lemma abstract_decode_at_inv (pp: int) (ab:t) l :
  abstract_decode_at pp ab = Just l →
  ∀ (instr : int) i,
    abstract_decode_instr_at ab pp instr = Some i →
    instr ∈ γ ((T.(load_single) ab pp):d) →
    List.In i l.
Proof.
  unfold abstract_decode_at, IntSet.fold.
  set (L := T.(load_single) ab pp).
  destruct (concretize_with_care_two_cases L) as [->|(instr_set&->&HI)]; simpl.
  discriminate.
  intros H instr i Hi HL.
  generalize (concretize_correct L instr HL). rewrite HI.
  clear HI.
  inv H.
  unfold γ. simpl.
  apply IntSet.P.fold_rec.
+ intros m m' a H H0 H1. rewrite H in H0. auto.
+ rewrite ZTree.gempty. intro; eq_some_inv.
+ intros m a k v H H0 H1 H2.
  rewrite ZTree.gsspec in H2. destruct ZTree.elt_eq.
  clear H2.
  assert (instr = Int.repr k). rewrite <- Int.repr_unsigned. subst.
  repeat rewrite Int.repr_unsigned. reflexivity.
  subst instr.
  rewrite Hi. left; reflexivity.
  clear Hi.
  destruct abstract_decode_instr_at; [right|]; auto.
Qed.

Definition ab_post_single (m: t) (pp: addr) (instr:ab_instruction * nat) : list ab_post_res :=
  match instr with
  | (AIHalt rs, z) => Hlt (T.(var) m rs) :: nil
  | (AISkip, z) => Run (pp + z) m :: nil
  | (AIGotoInd rs, z) => abstract_goto_ind m (T.(var) m rs)
  | (AIGotoCond f v, z) => abstract_goto_cond f m pp v
  | (AIGoto v, z) => abstract_goto_ind m v
  | (AIStore rs rd, z) => Run (pp + z) (store_many m (T.(var) m rd) (T.(var) m rs)) :: nil
  | (AILoad rs rd, z) =>
    match load_many m (T.(var) m rs) with
    | NotBot v => Run (pp + z) (T.(assign) m rd v) :: nil
    | Bot => nil
    end
  | (AICmp rs rd, z) => Run (pp + z) (T.(compare) m rs rd ) :: nil
  | (AIBinop op rs rd, z) => bot_cons (abstract_op op m rs rd) (Run (pp + z)) nil
  | (AICst v rd, z) => Run (pp + z) (T.(assign) m rd v) :: nil
  end.

Definition ab_post_many (pp: addr) (m:t) : list ab_post_res :=
  match abstract_decode_at pp m with
  | Just instr => flat_map (ab_post_single m pp) instr
  | All => GiveUp :: nil
  end.

(** Flow-sensitive analysis. *)
Import Containers.Maps.
Record vsa_state :=
{ worklist : list int
; result_fs : Map [ int, t ] (* one value per pp; unbound values are ⊥ *)
; result_hlt: d+⊥            (* final value *)
}.

Notation result_at_run := (fun (E:vsa_state) (pp:int) => find_bot E.(result_fs) pp).

Local Instance lifted_mem_wl : weak_lattice (t+⊥) := lift_bot_wl T.(as_wl).

Definition propagate (widenp:bool) (E:vsa_state) (n: ab_post_res) : vsa_state+⊤ :=
  match n with
  | GiveUp => All
  | Run n' ab =>
    let old := result_at_run E n' in
    let new := (if widenp then widen else join) old (NotBot ab) in
    if new ⊑ old
    then Just E
    else Just {| worklist := if List.in_dec LatticeSignatures.eq_dec n' E.(worklist)
                             then E.(worklist)
                             else n' :: E.(worklist)
               ; result_fs := match new with
                              | NotBot new' => (E.(result_fs))[ n' <- new' ]
                              | Bot => MapInterface.remove n' E.(result_fs)
                              end
               ; result_hlt := E.(result_hlt) |}
  | Hlt res =>
    let old := E.(result_hlt) in
    let new := (if widenp then widen else join) old (NotBot res) in
    if new ⊑ old
    then Just E
    else Just {| worklist := E.(worklist)
               ; result_fs := E.(result_fs)
               ; result_hlt := new
              |}
  end.

Variable widen_oracle : int → ab_post_res → bool.

Inductive ipvsa_res := ipvsa_top | ipvsa_fix (E:vsa_state) | ipvsa_cont (E:vsa_state).

Definition intraProceduralVSA_step (E:vsa_state) : ipvsa_res :=
  match worklist E with
  | nil => ipvsa_fix E (* fix point reached *)
  | n :: l =>
    match result_at_run E n with
    | NotBot ab_mc =>
      let r :=
      List.fold_left
      (fun acc res =>
        match acc with
          | ipvsa_top => ipvsa_top
          | ipvsa_fix E' (* cannot happen *)
          | ipvsa_cont E' =>
            match propagate (widen_oracle n res) E' res with
              | All => ipvsa_top
              | Just x => ipvsa_cont x
            end
        end)
      (ab_post_many n ab_mc)
      (ipvsa_cont {| worklist := l
                   ; result_fs := E.(result_fs)
                   ; result_hlt:= E.(result_hlt) |})
      in
      (*
      DebugNumDomain.print
        (GotoString.string_of_int n ++ ": " ++ to_string ab_mc)
      *)
        r
    | Bot => ipvsa_top (* this must not happen or propagate is bugged/misused *)
  end
end.

Fixpoint intraProceduralVSA_loop (fuel: nat) (E: vsa_state) : ipvsa_res :=
  match fuel with
  | O => ipvsa_cont E
  | S fuel' => match intraProceduralVSA_step E with
               | ipvsa_cont E' => intraProceduralVSA_loop fuel' E'
               | x => x
               end
  end.
(*
  well_founded_induction_type
    Plt_wf
    (λ _, vsa_state → ipvsa_res)
    (λ p F, match P_zerop p with
            | left _ => ipvsa_cont
            | right K => λ E, match intraProceduralVSA_step E with
                              | ipvsa_cont E' => F (Ppred p) (Plt_pred p K) E'
                              | x => x
                              end
            end).
*)

Definition intraProceduralVSA_init I : vsa_state :=
  {| worklist := Int.zero :: nil
   ; result_fs := ([])[ Int.zero <- I ]
   ; result_hlt := Bot
  |}.

Definition intraProceduralVSA (P: memory) (dom: list int) n : ipvsa_res :=
  intraProceduralVSA_loop n (intraProceduralVSA_init (init T P dom)).

End GOTOANALYSIS.

Section VALIDATE.

Variables t d: Type.
Variable (D: ab_machine_int d) (T: mem_dom t d) (G: gamma_op t machine_config).
Local Instance G_as_instance : gamma_op t machine_config := G.
Hypotheses (D_correct: ab_machine_int_correct D) (T_sound: mem_dom_sound T G).

Variable max_deref : N.

Import Containers.Maps.

Local Instance t_wl : weak_lattice t := T.(as_wl).
Local Instance ltd_wl : weak_lattice ((t * d)+⊥) := lift_bot_wl (WProd.make_wl T.(as_wl) _).

(* Abstract Environment. *)
Definition AbEnv : Type := (Map [int, t] * d+⊥)%type.

Definition ab_env_leb (x y: AbEnv) : bool :=
  match x, y with
  | (xr,xh), (yr,yh) => map_LE_dec leb xr yr && xh ⊑ yh
  end.

Definition ab_env_join (x y: AbEnv) : AbEnv :=
  match x, y with
  | (xr,xh), (yr, yh) => (map_join join xr yr, xh ⊔ yh)
  end.

Definition ab_env_widen (x y: AbEnv) : AbEnv :=
  match x, y with
  | (xr,xh), (yr, yh) => (map_join widen xr yr, xh ⊔ yh)
  end.

Definition fs_pl : pre_lattice AbEnv :=
  {| pl_leb := ab_env_leb
   ; pl_join x y := Just (ab_env_join x y)
   ; pl_widen x y := Just (ab_env_widen x y)
  |}.

Instance fs_gamma : gamma_op AbEnv machine_state :=
  λ x, let '(xr, xh) := x in
       λ m,
       match m with
       | ⌈res⌉ => res ∈ γ(xh)
       | Running mci => mci ∈ γ(find_bot xr mci.(pc))
       end.

Lemma fs_pl_sound : pre_lattice_spec fs_pl fs_gamma.
Proof.
  Hint Resolve as_int_adom.
  constructor.
- (* gamma monotone *)
  unfold γ. simpl.
  intros (xr,xh) (yr,yh). simpl.
  rewrite andb_true_iff. intros (R,H).
  intros [res|mci]; eapply gamma_monotone. apply lift_bot; eauto.
  destruct xh as [|xh]; destruct yh as [|yh]; trivial. apply lift_bot, as_adom. eauto.
  case_eq (map_LE_dec leb xr yr); intros LE K. 2: rewrite K in R; exfalso; discriminate.
  clear K R.
  specialize (LE mci.(pc)). unfold find_bot.
  case_eq ((xr)[mci.(pc)]); trivial. intros x Hx.
  destruct (LE x) as (y&Hy&Hxy). apply MF.find_mapsto_iff. auto.
  rewrite MF.find_mapsto_iff in Hy. rewrite Hy. auto.
- (* join sound *)
  intros (xr,xh) (yr,yh).
  unfold γ. simpl.
  intros [res|mci].
  destruct xh as [|xh]; destruct yh as [|yh]; simpl; try now intuition.
  unfold γ. simpl. eauto using join_sound.
  unfold γ. simpl. rewrite map_join_get.
  destruct (find_bot xr mci.(pc)); destruct (find_bot yr mci.(pc)); simpl; try now intuition.
  apply join_sound, as_adom. auto.
Qed.

Definition fs_adom : adom _ _ (weak_lattice_of_pre_lattice fs_pl) _ := adom_of_pre_lattice fs_pl_sound.

Definition abEnv_of_vsa_state (E: vsa_state t d) : AbEnv :=
  (E.(result_fs), E.(result_hlt)).

Instance instr_gamm : gamma_op (ab_instruction d) instruction :=
  λ a i,
  match a, i with
  | AICst v r, ICst v' r' => v' ∈ γ(v) ∧ r = r'
  | AIBinop op rs rd, IBinop op' rs' rd' => op = op' ∧ rs = rs' ∧ rd = rd'
  | AICmp rs rd, ICmp rs' rd' => rs = rs' ∧ rd = rd'
  | AILoad rs rd, ILoad rs' rd' => rs = rs' ∧ rd = rd'
  | AIStore rs rd, IStore rs' rd' => rs = rs' ∧ rd = rd'
  | AIGoto v, IGoto v' => v' ∈ γ(v)
  | AIGotoCond f v, IGotoCond f' v' => f' = f ∧ v' ∈ γ(v)
  | AIGotoInd rs, IGotoInd rs' => rs = rs'
  | AISkip, ISkip => True
  | AIHalt rs, IHalt rs' => rs = rs'
  | _, _ => False
  end.

Local Instance ListAsSet E E' `{G: gamma_op E E'} : gamma_op (list E) E' :=
  λ l e', ∃ e, List.In e l ∧ e' ∈ γ(e).

Remark flat_map_gamma {F E E'} `{gamma_op E E'} :
  ∀ f : F → list E,
  ∀ l : list F,
  ∀ x : E',
  (∃ y : F, List.In y l ∧ x ∈ γ(f(y))) →
  x ∈ γ (flat_map f l).
Proof.
  intros f l x (y & Y & (q & Q & R)).
  exists q. split. apply in_flat_map. vauto. exact R.
Qed.

Local Instance ProdGamma A B A' B' `{Ga: gamma_op A A'}
      `{Gb: gamma_op B B'} : gamma_op (A * B) (A' * B') :=
  λ ab a'b',
  let (a, b) := ab in let (a', b') := a'b' in
  a' ∈ γ(a) ∧ b' ∈ γ(b).

Local Instance IdGamma : gamma_op nat nat := @eq nat.
Local Instance OptGamm {A B: Type} `{gamma_op A B} : gamma_op A (option B) :=
  λ a b', match b' with Some b => b ∈ γ(a) | None => True end.

Lemma abstract_decode_at_sound :
  ∀ (m:machine_config) (ab:t) (pp: int),
    m ∈ γ(ab) →
    decode_from m.(mc_mem) pp ∈ γ(abstract_decode_at D T max_deref pp ab).
Proof.
  intros m ab pp Hm.
  destruct (decode_from m.(mc_mem) pp) as [i|] eqn: Hi.
  destruct (abstract_decode_at D T max_deref pp ab) as [|l] eqn: Hl.
  exact I.
  revert Hi.
  generalize (abstract_decode_at_inv T D_correct max_deref pp ab Hl (m.(mc_mem) pp)).
  pose proof (load_sound T_sound ab m Hm pp) as LOAD.
  unfold decode_from, abstract_decode_instr_at.
  intros H'. pose proof (λ j J, H' j J LOAD) as H; clear H'.

  destruct (split_instruction (m.(mc_mem) pp)) as (((type, arg), src), dst).
  repeat
  match goal with
  | |- appcontext[ match ?a with _ => _ end ] =>
    destruct a
  end;
  intros; eq_some_inv; subst;
  specialize (H _ eq_refl);
  (eexists; split; [exact H|]);
  repeat split;
  apply (load_sound T_sound); auto.
  exact I.
Qed.

Lemma abstract_decode_instr_at_complete ab mci m pp :
  mci ∈ γ(ab) →
  m = mci.(mc_mem) →
  decode_from m pp = None →
  abstract_decode_instr_at T ab pp (m pp) = None.
Proof.
  intros MCI M.
  unfold decode_from, abstract_decode_instr_at.
  destruct (split_instruction (m pp)) as (((type, arg), src), dst).
  repeat
  match goal with
  | |- appcontext[ match ?a with _ => _ end ] =>
    destruct a
  end;
    intros; eq_some_inv; auto.
Qed.

Local Instance AbPostResGamma : gamma_op (ab_post_res t d) machine_state :=
  λ r ms,
  match r, ms with
  | Run pp' ab, ⟨pp, f, r, m⟩ => pp = pp' ∧ {| pc := pp; mc_flg := f; mc_reg := r; mc_mem := m |} ∈ γ(ab)
  | Hlt v', ⌈v⌉ => v ∈ γ(v')
  | GiveUp, _ => True
  | _, _ => False
  end.

Local Open Scope goto_scope.

Local Coercion Running : machine_config >-> machine_state.
Lemma ab_post_many_correct (m: machine_config) (m': machine_state) (ab: t) :
  m ∈ γ(ab) →
  m =~> m' →
  m' ∈ γ(ab_post_many D T max_deref m.(pc) ab).
Proof.
  destruct m as [pp f r m]. simpl.
  intros M ST.
  unfold ab_post_many.
  destruct (abstract_decode_at D T max_deref pp ab) as [|instr] eqn: AD.
  eexists. vauto.
  pose proof (abstract_decode_at_sound pp M) as HL.
  rewrite AD in HL; clear AD.
  apply flat_map_gamma.
  inv ST; simpl in *;
  match goal with
  | H : decode_from _ _ = ⌊(_, ?z)⌋ |- _ =>
    rewrite H in HL;
    destruct HL as ((a & n) & Ha & (Ha' & ->));
    destruct a; try (exact (False_ind _ Ha'));
    eexists;
    (split;[exact Ha|]); clear Ha
  end;
  simpl;
  try
  match goal with
  | |- γ (_ :: nil) _ => eexists; split;[left; reflexivity|]
  end.
+ destruct Ha' as (Ha' & ->).
  split. reflexivity.
  apply (assign_sound T_sound).
  vauto.
+ destruct Ha' as (-> & ->).
  split. reflexivity.
  apply (compare_sound T_sound).
  exists f. simpl. intuition.
  exact (flow_insensitive T_sound _ _ M (pp+z)).
+ destruct Ha' as (-> & -> & ->).
  assert (RS := var_sound T_sound _ _ M rs).
  assert (RD := var_sound T_sound _ _ M rd). simpl in *.
  generalize (forward_int_binop_sound (op:=op) (var T ab rs) (var T ab rd)).
  unfold abstract_op in *.
  case_eq (forward_int_binop op (var T ab rs) (var T ab rd)).
  intros _ X; exfalso; refine (X (eval_int_binop op (r rs) (r rd)) _).
  vauto.
  intros x X Y.
  eexists. split. left; reflexivity.
  split. reflexivity.
  apply (assign_sound T_sound).
  eexists. exists (eval_int_binop op (r rs) (r rd)). split.
  apply (flow_insensitive T_sound _ _ M (eval_int_binop op (r rs) (r rd))). split.
  apply Y. vauto.
  simpl. vauto.
+ destruct Ha' as ( -> & -> ).
  unfold load_many.
  destruct (concretize_with_care_two_cases D max_deref (var T ab rs)) as [H|(src&H&SRC)];
  rewrite H.
  * simpl. eexists. split. left; reflexivity.
    split. reflexivity.
    apply assign_sound; auto.
    eexists _, (m (r rs)). split. exact M. simpl.
    split. apply gamma_top; eauto. auto.
  * generalize (concretize_correct (var T ab rs)).
    rewrite SRC. intros Hsrc.
    specialize (Hsrc _ (var_sound T_sound _ _ M rs)). simpl in *.
    generalize (load_many_aux_sound D T ab Hsrc).
    generalize (load_sound T_sound _ _ M (r rs)). simpl.
    intros U V. specialize (V _ U).
    destruct (load_many_aux D T ab src) as [|q]. destruct V.
    simpl. eexists. split. left; reflexivity.
    split. reflexivity.
    apply assign_sound; auto.
    vauto.
+ destruct Ha' as ( -> & -> ).
  split. reflexivity.
  unfold store_many.
  destruct (concretize_with_care_two_cases D max_deref (var T ab rd)) as [H|(dst&H&DST)];
  rewrite H.
  apply gamma_top, as_adom; auto.
  set (mc := {| pc := pp; mc_flg := f; mc_reg := r; mc_mem := m |}).
  rewrite union_list_map_correct.
  eapply union_list_correct.
  apply join_sound, as_adom; auto.
  apply List.in_map.
  apply IntSet.as_list_iff.
  generalize (concretize_correct (var T ab rd) (mc.(mc_reg) rd) (var_sound T_sound _ _ M _)).
  rewrite DST. intros X. red in X. simpl in X. eauto.
  apply T_sound.(store_sound).
  exists m, (r rs). simpl. split.
  generalize (flow_insensitive T_sound _ _ M (pp+z)). exact id.
  split. change r with mc.(mc_reg). apply T_sound.(var_sound). eauto.
  rewrite Int.repr_unsigned. auto.
+ red in Ha'. simpl in Ha'.
  destruct (abstract_goto_ind_sound D_correct max_deref ab tgt)
           as [GIVEUP|DEREF].
  rewrite GIVEUP. eexists; split. vauto. exact I.
  specialize (DEREF _ Ha').
  eexists. split. exact DEREF.
  split. reflexivity.
  generalize (flow_insensitive T_sound _ _ M v). simpl. exact id.
+ destruct Ha' as ( <- & Ha' ).
  set (ab' := assume_mem T ab (pp+1) v).
  assert (Assume (γ ab') c (f c) {| pc := pp; mc_flg := f; mc_reg := r; mc_mem := m |}) as Q.
  { split. 2: reflexivity. unfold ab'. apply assume_mem_sound; auto.
    exists m. split. exact M.
    simpl. intros a. unfold upd. destruct (LatticeSignatures.eq_dec a (pp+1)); auto.
    subst. revert H4. clear. unfold decode_from.
    destruct split_instruction as (((type, arg), src), dst).
    repeat
      match goal with
      | |- appcontext[ match ?a with _ => _ end ] =>
        destruct a
      end;
    intros; eq_some_inv; try discriminate.
    inv H. reflexivity.
  }
  generalize (assume_sound T_sound (f := c) (b := f c) ab' Q).
  generalize (assume_sound T_sound (f := c) (b := f c) ab (conj M eq_refl)).
  destruct (abstract_goto_cond_sound T D_correct max_deref c ab pp tgt)
    as [GIVEUP|(LE&NLE)].
  * rewrite GIVEUP.
    intros _ _. eexists. vauto.
  * specialize (LE _ Ha').
    fold ab' in LE.
    destruct (f c).
    { destruct (assume T ab' c true) as [|R'']. exact (λ _, False_ind _).
      intros _ K.
      generalize (flow_insensitive T_sound _ _ K v). simpl.
      intros K'. clear K.
      eexists. split. exact LE. vauto.
    }
    { destruct (assume T ab c false) as [|R'']. exact (False_ind _).
      intros K _.
      generalize (flow_insensitive T_sound _ _ K (pp + z)). simpl.
      intros K'. clear K.
      eexists. split. exact NLE.
      assert (z = 2%nat).
      revert H4; clear.
      unfold decode_from.
      destruct split_instruction as (((type, arg), src), dst).
      repeat
        match goal with
        | |- appcontext[ match ?a with _ => _ end ] =>
          destruct a
        end;
        intros; eq_some_inv; try discriminate.
      auto.
      subst.
      vauto.
    }

+ assert (RD := var_sound T_sound _ _ M rd).
  red in Ha'. simpl in Ha'. subst r0.
  simpl in RD.
  destruct (abstract_goto_ind_sound D_correct max_deref ab (var T ab rd))
           as [GIVEUP|DEREF].
  * rewrite GIVEUP. eexists. vauto.
  * specialize (DEREF _ RD).
    eexists. split. exact DEREF.
    split. reflexivity.
    exact (flow_insensitive T_sound _ _ M (r rd)).

+ split. reflexivity.
  exact (flow_insensitive T_sound _ _ M (pp+z)).

+ destruct Ha'.
  change r with (mc_reg {| pc := pp; mc_flg := f; mc_reg := r; mc_mem := m |}).
  eapply var_sound; eauto.
Qed.

Corollary ab_post_many_correct' m m' (ab: t) :
  m ∈ γ(ab) → Running m =~> m' →
  ∃ r, List.In r (ab_post_many D T max_deref m.(pc) ab) ∧
       m' ∈ γ(r).
Proof.
  refine (λ A B, match ab_post_many_correct A B with ex_intro r R => ex_intro _ r R end).
Qed.

Definition validate_fixpoint (P: memory) (dom: list addr) (E: AbEnv) : bool :=
  (* contains initial state *)
  NotBot (init T P dom) ⊑ find_bot (fst E) Int.zero
    &&
  MF.for_all
    (fun (pp: addr) (ab: t) =>
       List.forallb
         (fun abr : ab_post_res t d =>
            match abr with
            | Run pp' ab' => NotBot ab' ⊑ find_bot (fst E) pp'
            | Hlt res => NotBot res ⊑ snd E
            | GiveUp => false
            end
         )
         (ab_post_many D T max_deref pp ab)
    )
    (fst E).

Theorem validate_correct : forall P dom E,
  validate_fixpoint P dom E = true →
  ⟦ P ⟧ ⊆ γ(E).
Proof.
  unfold validate_fixpoint.
  intros P dom E.
  rewrite andb_true_iff.
  intros [I ST].
  rewrite MF.for_all_iff in ST. 2: intuition.
  apply (CompleteLattice.lfp_least_postfixpoint _ _ _ (semantics_fun_mon P)). simpl.
  intros msi [INIT|(msi' & Hmsi' & POST)].
- (* initial state *)
  destruct msi as [|[pp0 m r f]]. elim INIT.
  destruct INIT as (-> & ->).
  destruct E as (xr,xh). red. simpl in *.
  destruct (find_bot xr). eq_some_inv.
  eapply (gamma_monotone T_sound.(as_adom)). eapply I. apply gamma_init; auto.
  vauto.

- (* post *)
  destruct msi' as [res|mci'].
  exfalso. set (diag x := match x with ⌈_⌉ => False | _ => ⌈res⌉ =~> msi end).
  change (diag ⌈res⌉). case POST; auto.
  destruct E as (Erun, Ehlt).
  red in Hmsi'. simpl in Hmsi'.
  unfold find_bot in Hmsi'.
  case_eq ((Erun)[pc mci']);
    [intros R|]; intros HR; rewrite HR in Hmsi'.
  2: now exfalso.
  red in Hmsi'. simpl in Hmsi'.
  generalize HR. rewrite <- MF.find_mapsto_iff. intros HR'.
  generalize (ST _ _ HR'). rewrite forallb_forall. intros ST'. clear HR'. clear ST.

  destruct (ab_post_many_correct Hmsi' POST) as (res & IN & RES).
  specialize (ST' res IN). clear IN.
  destruct res as [pp' ab'|res|].
  destruct msi. destruct RES.
  destruct c as [pp r f m]. destruct RES as ( -> & RES).
  red. simpl.
  apply (gamma_monotone (lift_bot T_sound.(as_adom)) ST'). auto.
  destruct msi.
  destruct Ehlt as [|?]; simpl in ST'. eq_some_inv.
  apply (gamma_monotone as_int_adom ST'). auto.
  destruct RES.
  eq_some_inv.
Qed.

  Definition check_safety (E': AbEnv) : bool :=
    let run := fst E' in
    MF.for_all
      (λ pp mc,
       match concretize_with_care D max_deref (T.(load_single) mc pp) with
       | All => false (* top, cannot prove safety *)
       | Just ab_instr =>
         IntSet.forallb
           (λ i, match abstract_decode_instr_at T mc pp (Int.repr i) with
                 | Some _ => true
                 | None => false
                 end)
           ab_instr
       end)
      run.

Lemma check_safety_not_stuck (E': AbEnv) :
  check_safety E' = true →
  ∀ s, γ(E') s → ¬ stuck s.
Proof.
  unfold check_safety. rewrite MF.for_all_iff. 2: now intuition.
  intros H s. destruct E' as (run, hlt). unfold γ. simpl.
  destruct s as [res|[p f r m]]. exact (λ _, id).
  unfold γ. simpl. unfold find_bot. case_eq ((run)[p]). 2: easy.
  intros o Hp Ho. apply MF.find_mapsto_iff in Hp.
  specialize (H _ _ Hp).
  destruct (concretize_with_care_two_cases D max_deref (T.(load_single) o p)) as [K|(ab_instr&K&U)];
    rewrite K in H; clear K.
  exfalso; discriminate.
  generalize (concretize_correct).
  generalize (load_sound T_sound _ _ Ho p). unfold mc_mem. intros X Y; specialize (Y _ _ X).
  rewrite U in Y. unfold γ in Y. simpl in Y.
  eapply IntSet.forallb_forall in H. 2: exact Y.
  simpl in H. rewrite Int.repr_unsigned in H.
  destruct (decode_from m p) as [(i, z)|] eqn: EQ.
  fold (stuck ⟨ p, f, r, m ⟩).
  rewrite stuck_is_decode_failure.
  congruence.
  rewrite (abstract_decode_instr_at_complete (m := m) p Ho eq_refl EQ) in H.
  eq_some_inv.
Qed.

Theorem check_safety_sound: ∀ P E, ⟦ P ⟧ ⊆ γ(E) →
  check_safety E = true → safe P.
Proof.
  intros P E A S s REACH.
  apply (check_safety_not_stuck E S), A, (reachable_in_sem P s REACH).
Qed.

Corollary safety_check P dom E:
  validate_fixpoint P dom E = true →
  check_safety E = true →
  safe P.
Proof.
  eauto using check_safety_sound, validate_correct.
Qed.

End VALIDATE.

Section ValuePartitionning.

Variables t d: Type.
Variables (D: ab_machine_int d) (T: mem_dom t d) (G: gamma_op t machine_config).
Hypothesis D_correct : ab_machine_int_correct D.
Hypothesis T_correct : mem_dom_sound T G.

Local Instance vp_t_wl : weak_lattice t := T.(as_wl).
Local Instance vp_ltd_wl : weak_lattice ((t * d)+⊥) := lift_bot_wl (WProd.make_wl T.(as_wl) _).

Variable δ : t → int.
Variable max_deref : N.

Import Containers.Maps.

Record vpstate :=
  { vp_worklist : list (int * int) (* (pp, δ(x)) *)
  ; vp_run : Map [ int, Map [ int, t ] ] (* unbound is ⊥ *)
  ; vp_hlt : d+⊥
  }.

Definition vpInit (I: t) : vpstate :=
  let v := δ I in
  {| vp_worklist := (Int.zero, v)::nil
   ; vp_run := ([])[ Int.zero <- ([])[ v <- I ] ]
   ; vp_hlt := Bot
  |}.

Inductive vpresult := VP_top | VP_fix (e: vpstate) | VP_cont (e: vpstate).

Definition vpPropagate (widenp: bool) (succ: ab_post_res t d) (E: vpstate) : vpstate+⊤ :=
  match succ with
  | GiveUp => All
  | Run pp ab =>
      let v := δ ab in
       let old := do_bot m <- find_bot E.(vp_run) pp; find_bot m v in
       let new := (if widenp then widen else join) old (NotBot ab) in
       if new ⊑ old
       then Just E
       else
         match new with
         | Bot => DebugAbMachineNonrel.print "anomaly: vpPropagate" (Just E) (* can this happen *)
         | NotBot new' =>
             let v' := δ new' in
             let m' := match find_bot E.(vp_run) pp with NotBot m' => m' | Bot => [] end in
             Just {| vp_worklist :=
                       if List.in_dec LatticeSignatures.eq_dec (pp, v') E.(vp_worklist)
                       then E.(vp_worklist)
                       else (pp, v') :: E.(vp_worklist)
                   ; vp_run := (E.(vp_run)) [ pp <- (m') [ v' <- new' ] ]
                   ; vp_hlt := E.(vp_hlt) |}
         end
  | Hlt res =>
    let old := E.(vp_hlt) in
    let new := (if widenp then widen else join) old (NotBot res) in
    if new ⊑ old
    then Just E
    else Just {| vp_worklist := E.(vp_worklist)
               ; vp_run := E.(vp_run)
               ; vp_hlt := new
              |}
  end.

Variable widen_oracle : int → ab_post_res t d → bool.

Definition vpStep (E: vpstate) : vpresult :=
  match E.(vp_worklist) with
  | nil => VP_fix E
  | (pp, v) :: wl =>
    match find_bot E.(vp_run) pp with
    | NotBot m =>
      match find_bot m v with
      | NotBot ab_mc =>
        let next : list (ab_post_res t d) := ab_post_many D T max_deref pp ab_mc in
        let r := List.fold_left
                   (λ acc res, toplift_bind
                               (vpPropagate (widen_oracle pp res) res)
                               acc)
                   next
                   (Just {| vp_worklist := wl
                          ; vp_run := E.(vp_run)
                          ; vp_hlt := E.(vp_hlt) |}) in
        match r with
        | All => VP_top
        | Just E' => VP_cont E'
        end
      | Bot => VP_top (* should not happen *)
      end
    | Bot => VP_top (* should not happen *)
    end
  end.

Fixpoint vpLoop (fuel: nat) (E: vpstate) : vpresult :=
  match fuel with
  | O => VP_cont E
  | S fuel' => match vpStep E with
               | VP_cont E' => vpLoop fuel' E'
               | x => x
               end
  end.

Definition vpAnalysis (P: memory) (dom: list int) n : vpresult :=
  vpLoop n (vpInit (init T P dom)).

Definition vpAbEnv : Type := (Map [int, Map [int, t] ] * d+⊥)%type.

Definition vp_ab_env_leb (x y: vpAbEnv) : bool :=
  match x, y with
  | (xr,xh), (yr,yh) => map_LE_dec (map_LE_dec leb) xr yr && xh ⊑ yh
  end.

Definition vp_ab_env_join (x y: vpAbEnv) : vpAbEnv :=
  match x, y with
  | (xr,xh), (yr, yh) => (map_join (map_join join) xr yr, xh ⊔ yh)
  end.

Definition vp_pl : pre_lattice vpAbEnv :=
  {| pl_leb := vp_ab_env_leb
   ; pl_join x y := Just (vp_ab_env_join x y)
   ; pl_widen x y := All
  |}.

Instance vp_gamma : gamma_op vpAbEnv machine_state :=
  λ x, let '(xr, xh) := x in
       λ m,
       match m with
       | ⌈res⌉ => res ∈ γ(xh)
       | Running mci =>
         ∃ v,
           γ
             (do_bot m' <- find_bot xr mci.(pc);
              find_bot m' v)
             mci
       end.

Lemma vp_pl_sound : pre_lattice_spec vp_pl vp_gamma.
Proof.
  Hint Resolve as_int_adom T_correct.(as_adom).
  constructor.
- (* gamma monotone *)
  intros (xr,xh) (yr,yh). unfold γ. simpl.
  rewrite andb_true_iff.
  destruct (@map_LE_dec) as [R|]. 2: intros (?,_); exfalso; discriminate.
  intros (_,H).
  intros [res|mci]. eapply gamma_monotone. apply lift_bot; eauto.
  destruct xh as [|xh]; destruct yh as [|yh]; trivial. simpl in *.
  intros (v & V). unfold find_bot in *.
  case_eq ((xr)[mci.(pc)]). 2: intros A; rewrite A in V; elim V.
  intros m' Hm'. rewrite Hm' in V. simpl in V. rewrite <- MF.find_mapsto_iff in Hm'.
  case_eq ((m')[v]). 2: intros A; rewrite A in V; elim V.
  intros z Hz. rewrite Hz in V. rewrite <- MF.find_mapsto_iff in Hz.
  destruct (R mci.(pc) _ Hm') as (m'' & Hm'' & Hm'm'').
  simpl. apply MF.find_mapsto_iff in Hm''. rewrite Hm''. simpl.
  destruct (@map_LE_dec) as [LE|]. 2: exfalso; discriminate. clear Hm'm''.
  destruct (LE v _ Hz) as (z' & Hz' & Hzz').
  exists v. apply MF.find_mapsto_iff in Hz'. rewrite Hz'. eapply (gamma_monotone T_correct.(as_adom)); eauto.
- (* join sound *)
  intros (xr,xh) (yr,yh).
  unfold γ. simpl. unfold γ. simpl.
  intros [res|mci].
  destruct xh as [|xh]; destruct yh as [|yh]; simpl; try now intuition.
  apply join_sound; auto.
  rewrite map_join_get.
  destruct (find_bot xr mci.(pc)) as [|r];
    destruct (find_bot yr mci.(pc)) as [|l];
    simpl; try now intuition.
  now intros [(_,())|].
  now intros [|(_,())].
  intros [(v,V)|(v,V)]; exists v; rewrite map_join_get;
  destruct (find_bot r v); destruct (find_bot l v); try (now intuition);
  apply join_sound; intuition; auto.
Qed.

Definition vpAbEnv_of_vpstate (E: vpstate) : vpAbEnv :=
  (E.(vp_run), E.(vp_hlt)).

Definition vp_validate_fixpoint (P: memory) (dom: list int) (E: vpAbEnv) : bool :=
  (* contains initial state *)
  let I := init T P dom in
  let iv := δ I in
    NotBot I ⊑ (do_bot m <- find_bot (fst E) Int.zero; find_bot m iv)
    &&
    MF.for_all
    (fun (pp: int) (m: Map [ int , t ]) =>
       MF.for_all
         (fun (_: int) (ab: t) =>
            List.forallb
              (fun abr : ab_post_res t d =>
                 match abr with
                 | Run pp' ab' =>
                   match find_bot (fst E) pp' with
                   | NotBot q => NotBot ab' ⊑ find_bot q (δ ab')
                   | _ => false
                   end
                 | Hlt res => NotBot res ⊑ snd E
                 | GiveUp => false
                 end
              )
              (ab_post_many D T max_deref pp ab)
         )
         m
    )
    (fst E).

Definition forget_vp (E: vpAbEnv) : AbEnv t d :=
  let fs : Map [ int, t ] :=
      map (fun m =>
             match map_any m with
             | inleft (exist kv _) => fold (fun _ ab acc => acc ⊔ ab) m (snd kv)
             | inright _ => ⊤
             end) (fst E) in
  (fs, snd E).

Local Open Scope goto_scope.
Theorem vp_validate_correct : forall P dom E,
  vp_validate_fixpoint P dom E = true →
  ⟦ P ⟧ ⊆ γ(E).
Proof.
  unfold vp_validate_fixpoint.
  intros P dom (Erun, Ehlt).
  rewrite andb_true_iff.
  intros [I ST]. simpl in I.
  rewrite MF.for_all_iff in ST. 2: intuition.
  apply (CompleteLattice.lfp_least_postfixpoint _ _ _ (semantics_fun_mon P)). simpl.
  intros msi [INIT|(msi' & Hmsi' & POST)].
- (* initial state *)
  destruct msi as [|[pp0 m r f]]. elim INIT.
  destruct INIT as (-> & ->).
  exists (δ (init T P dom)). simpl.
  destruct (find_bot Erun) as [|x]. discriminate. simpl in *.
  destruct (find_bot x). eq_some_inv.
  red. simpl.
  eapply gamma_monotone. auto. exact I. apply gamma_init; auto.
  vauto.

- clear I.
  destruct msi' as [res|mci'].
  exfalso. set (diag x := match x with ⌈_⌉ => False | _ => ⌈res⌉ =~> msi end).
  change (diag ⌈res⌉). case POST; auto.
  destruct Hmsi' as (δmsi, Hmsi').
  unfold find_bot in Hmsi'.
  case_eq ((Erun)[pc mci']);
    [intros R'|]; intros HR'; rewrite HR' in Hmsi'.
  2: now exfalso.
  generalize HR'. rewrite <- MF.find_mapsto_iff. intros HR1.
  generalize (ST _ _ HR1). rewrite MF.for_all_iff. 2: intuition. intros ST''. clear HR1 ST.
  simpl in Hmsi'.
  case_eq ((R')[δmsi]);
    [intros R|]; intros HR; rewrite HR in Hmsi'.
  2: now exfalso.
  generalize HR. rewrite <- MF.find_mapsto_iff. intros HR1.
  generalize (ST'' _ _ HR1). rewrite forallb_forall. intros ST'. clear HR1 ST''.

  destruct (ab_post_many_correct D_correct T_correct max_deref R Hmsi' POST) as (res & IN & RES).
  specialize (ST' res IN). clear IN.
  destruct res as [pp' ab'|res|].
  destruct msi. destruct RES.
  destruct c as [pp r f m]. destruct RES as ( -> & RES).
  red. simpl.
  simpl in ST'.
  destruct (find_bot Erun pp'). eq_some_inv. simpl.
  exists (δ ab').
  destruct (find_bot x (δ ab')). eq_some_inv.
  exact (gamma_monotone T_correct.(as_adom) ST' _ RES).
  destruct msi.
  destruct Ehlt as [|?]; simpl in ST'. eq_some_inv.
  exact (gamma_monotone as_int_adom ST' _ RES).
  destruct RES.
  eq_some_inv.
Qed.

Existing Instance fs_gamma.
Lemma forget_morph E : γ(E) ⊆ γ(forget_vp E).
Proof.
  destruct E as (Erun, Ehlt). unfold γ. simpl.
  intros [res|mci]. now destruct Ehlt.
  unfold find_bot.
  rewrite MF.map_o.
  case_eq ((Erun)[mci.(pc)]). 2: intros _ (_,()).
  simpl.
  intros m' Hm' (v& V).
  case_eq ((m')[v]);[intros ab|]; intros Hab; rewrite Hab in V.
  2: intuition.
  clear Hm'.
  destruct (map_any m') as [((k,any),H)|]. 2: apply gamma_top; auto.
  simpl in *.
  generalize dependent mci.
  generalize dependent ab.
  generalize dependent v.
  apply MF.fold_rec_bis.
  intros m m'0 a H0 H1 v ab. rewrite <- H0. apply H1.
  intros v ab Hab. exfalso. rewrite MF.empty_o in Hab. eq_some_inv.
  intros v' e a m'0 H0 H1 H2 v ab.
  case (eq_dec v' v); intros U.
  rewrite MF.add_eq_o; auto.
  intros X; injection X; clear X. intros ->. repeat intro. apply join_sound; auto.
  rewrite MF.add_neq_o; auto.
  intros X; generalize (H2 _ _ X).
  intros H3 mci V. apply join_sound; eauto.
Qed.

Let check_safety := check_safety D T max_deref.

Corollary vp_safety_check P dom E:
  vp_validate_fixpoint P dom E = true →
  check_safety (forget_vp E) = true →
  safe P.
Proof.
  intros V S.
  eapply check_safety_sound; eauto.
  intros x H. apply forget_morph.
  eapply vp_validate_correct; eassumption.
Qed.

End ValuePartitionning.
