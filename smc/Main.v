Require Import
  Utf8
  Util AdomLib
  Goto GotoSem AbGoto DebugMemDom
  GotoAnalysis
  FirstGotoAnalysis.

Theorem first_analysis_sound (P: memory) (dom: list addr) (fuel: nat) (ab_num: num_domain_index) :
  ∀ mem_debug max_deref widen_oracle,
  first_analysis ab_num mem_debug max_deref widen_oracle P dom fuel ≠ None →
  safe P.
Proof.
  intros mem_debug max_deref widen_oracle.
  unfold first_analysis.
  destruct (first_vsa ab_num mem_debug max_deref widen_oracle P dom fuel);
    try refine (λ X, False_ind _ (X eq_refl)).
  unfold first_validate, first_check_safety.
  match goal with |- appcontext[@validate_fixpoint ?t ?d ?D ?T ?w ?x ?y ?z] =>
                  generalize (λ S, @validate_correct t d D T
                                        (toplift_gamma (abmc_gamma D (IntSet.of_list dom)))
                                        (num_dom_of_index ab_num).(correct) S
                                        max_deref P dom (abEnv_of_vsa_state E))
  end.
  destruct validate_fixpoint.
  2: exact (λ _ X, False_ind _ (X eq_refl)).
  intros A. simpl.
  generalize (λ S, @check_safety_sound _ _ _ _ _ (num_dom_of_index ab_num).(correct) S max_deref P (abEnv_of_vsa_state E) (A S eq_refl)). clear A.
  destruct check_safety.
  2: exact (λ _ X, False_ind _ (X eq_refl)).
  intros H _. clear -H.
  eapply H. 2: exact eq_refl.
  destruct mem_debug.
  apply debug_mem_dom_sound, ab_machine_config_mem_dom_sound, correct.
  apply ab_machine_config_mem_dom_sound, correct.
Qed.

(* Print Assumptions first_analysis_sound. *)

Theorem analysis_sound (P: memory) dom fuel:
  ∀ idx mem_debug max_deref widen_oracle δ,
  analysis idx mem_debug max_deref widen_oracle P dom δ fuel ≠ None →
  safe P.
Proof.
  intros idx mem_debug max_deref widen_oracle δ.
  unfold analysis.
  destruct (vp_analysis idx mem_debug max_deref widen_oracle P dom δ fuel);
    try refine (λ X, False_ind _ (X eq_refl)).
  unfold vp_validate, vp_check_safety.
  match goal with |- appcontext[@vp_validate_fixpoint ?t ?d ?D ?T ?w ?x ?y ?z] =>
                  generalize (λ S, @vp_safety_check t d D T
                                        (toplift_gamma (abmc_gamma D (IntSet.of_list dom)))
                                        (num_dom_of_index idx).(correct) S δ
                                        max_deref widen_oracle P dom (vpAbEnv_of_vpstate e))
  end.
  destruct vp_validate_fixpoint.
  2: exact (λ _ X, False_ind _ (X eq_refl)).
  destruct check_safety.
  2: exact (λ _ X, False_ind _ (X eq_refl)).
  intros H _. clear -H.
  refine (H _ eq_refl eq_refl).
  destruct mem_debug.
  apply debug_mem_dom_sound, ab_machine_config_mem_dom_sound, correct.
  apply ab_machine_config_mem_dom_sound, correct.
Qed.

(* Print Assumptions analysis_sound. *)
