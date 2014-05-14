Require Import
  Utf8 Coqlib
  Integers ToString
  LatticeSignatures AdomLib
  AbMachineNonrel
  DebugAbMachineNonrel
  IntSet IntSetDom StridedIntervals
  Goto GotoSem GotoString AbGoto GotoAnalysis
  DebugMemDom
  AbCfg.
Require
  AbCfg2.

Unset Elimination Schemes.

Inductive num_domain_index :=
| ND_SSI
| ND_FinSet
| ND_Debug (i: num_domain_index)
.

Record correct_num_dom := ND
  {
   d : Type;
   as_dom: ab_machine_int d;
   str: ToString d;
   correct: ab_machine_int_correct as_dom
  }.

Fixpoint num_dom_of_index (i: num_domain_index) : correct_num_dom :=
  match i with
  | ND_SSI => ND strided_interval ssi_dom ssiToString ssi_num_dom_correct
  | ND_FinSet => ND fint_set int_set_dom _ int_set_dom_correct
  | ND_Debug i' =>
    let nd := num_dom_of_index i' in
    ND nd.(d) (@debug_ab_machine_int _ nd.(as_dom) nd.(str)) nd.(str) (@debug_ab_machine_int_correct _ _ nd.(correct) _)
  end.

Section FirstTry.

Variable idx : num_domain_index.
Variable mem_debug : bool.

Let dDT := num_dom_of_index idx.
Let d : Type := dDT.(d).
Let D : ab_machine_int d := dDT.(as_dom).
Definition string_of_dom : ToString d := dDT.(str).

Let t : Type := (ab_machine_config d)+⊤.

Existing Instance string_of_dom.
Existing Instance abmc_toString.
Instance T_toString : ToString t := noitpo_toString _.

Variable max_deref : N.
Variable widen_oracle : int → ab_post_res t d → bool.

Context (P : memory)
        (dom: list int).

Let dom_set : int_set := IntSet.of_list dom.

Let T : mem_dom t d :=
  let m := ab_machine_config_mem_dom D dom_set in
  if mem_debug then debug_mem_dom m
  else m.

Definition first_vsa fuel : ipvsa_res t d :=
  intraProceduralVSA D T max_deref widen_oracle P dom fuel.

Definition first_validate (E: vsa_state t d) : bool :=
  validate_fixpoint D T max_deref P dom (abEnv_of_vsa_state E).

Definition first_compute_cfg (E: vsa_state t d) fuel : option (node_graph d) :=
  compute_cfg t d D T E.(result_fs) max_deref fuel.

Definition first_check_safety (E: vsa_state t d) : bool :=
  check_safety D T max_deref (abEnv_of_vsa_state E).

Definition first_analysis fuel : option (node_graph d) :=
  match first_vsa fuel with
  | ipvsa_fix E => (* putative fixpoint E found *)
    if first_validate E && first_check_safety E
    then (* E is correct w.r.t. P and is safe *)
      first_compute_cfg E fuel
    else None
  | _ => None
  end.

Definition vp_analysis (δ: t → int) fuel : vpresult t d :=
  vpAnalysis D T δ max_deref widen_oracle P dom fuel.

Definition vp_validate (δ: t → int) (E: vpstate t d) : bool :=
  vp_validate_fixpoint D T δ max_deref P dom (vpAbEnv_of_vpstate E).

Definition vp_compute_cfg (E: vpstate t d) fuel : option (node_graph d) :=
  compute_cfg t d D T (fst (forget_vp T (vpAbEnv_of_vpstate E))) max_deref fuel.

Definition vp_compute_cfg2 (δ: t → int) (v: int) (E: vpstate t d) fuel : option (AbCfg2.node_graph d) :=
  AbCfg2.compute_cfg t d D T δ E.(vp_run) max_deref fuel v.

Definition vp_check_safety (E: vpstate t d) : bool :=
  check_safety D T max_deref (forget_vp T (vpAbEnv_of_vpstate E)).

Definition analysis (δ: t → int) fuel : option (AbCfg2.node_graph d) :=
  match vp_analysis δ fuel with
  | VP_fix E => (* putative fixpoint E found *)
    if vp_validate δ E && vp_check_safety E
    then (* E is correct w.r.t. P and is safe *)
      vp_compute_cfg2 δ (δ (init T P dom)) E fuel
    else None
  | _ => None
  end.

Existing Instance D.
Definition mem_cell_partition (x: Z) (m: t) : int :=
  match (
  do_top l <- concretize_with_care _ 1%N (T.(load_single) m (Int.repr x));
  match TreeAl.ZTree.elements l with
  | (x, tt) :: nil => Just (Int.repr x)
  | _ => All
  end)
  with
  | Just res => res
  | All => Int.repr (-1000)
  end.

Definition reg_partition (r: register) (m: t) : int :=
  match (
  do_top l <- concretize_with_care _ 1%N (var T m r);
  match TreeAl.ZTree.elements l with
  | (x, tt) :: nil => Just (Int.repr x)
  | _ => All
  end)
  with
  | All => Int.repr (-1)
  | Just e => e
  end.

Definition print_run (s: vpstate t d) : unit :=
  print (map_to_string string_of_int (map_to_string string_of_int to_string) s.(vp_run)) tt.

Definition print_hlt (s: vpstate t d) : unit :=
  print (to_string s.(vp_hlt)) tt.

End FirstTry.
