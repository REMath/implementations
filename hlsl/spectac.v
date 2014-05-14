(*===========================================================================
    Tactics for the specification logic
  ===========================================================================*)
Ltac type_of t := type of t (* ssreflect bug workaround *).
Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq.
Require Import SPred spec septac.
Require Import safe procstate.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section SpecSplit.

  Definition specsplit (S S1 S2: spec) := S1 //\\ S2 |-- S.

  Lemma specsplit_and S1 S2:
    specsplit (S1 //\\ S2) S1 S2.
  Proof. red. done. Qed.

  Lemma specsplit_at S R S1 S2:
    specsplit S S1 S2 ->
    specsplit (S @ R) (S1 @ R) (S2 @ R).
  Proof.
    rewrite /specsplit => H. rewrite <-H. by autorewrite with push_at.
  Qed.

  Lemma specsplit_reads S R S1 S2:
    specsplit S S1 S2 ->
    specsplit (S <@ R) (S1 <@ R) (S2 <@ R).
  Proof.
    rewrite /specsplit => H. rewrite <-H. by rewrite spec_reads_and.
  Qed.

  Lemma specsplit_impl S S' S1 S2:
    specsplit S S1 S2 ->
    specsplit (S' -->> S) (S' -->> S1) (S' -->> S2).
  Proof.
    rewrite /specsplit => H. rewrite <-H. apply: limplAdj. rewrite landA.
    apply: limplL; first exact: landL2. cancel1. exact: landAdj.
  Qed.

  Lemma specsplit_do C S S1 S2:
    specsplit S S1 S2 ->
    C |-- S1 ->
    C |-- S2 ->
    C |-- S.
  Proof. rewrite /specsplit. move=> H. rewrite <-H. exact: landR. Qed.
End SpecSplit.

Hint Extern 1 => eapply (@specsplit_at _ _ _ _) : specsplit.
Hint Extern 1 => eapply (@specsplit_reads _ _ _ _) : specsplit.
Hint Extern 1 => eapply (@specsplit_impl _ _ _ _) : specsplit.
Hint Resolve specsplit_and : specsplit.

(* This tactic looks deep inside the goal to find a conjunction in a positive
   position. It then generates two subgoals; one for each conjunct. *)
Ltac specsplit :=
  eapply specsplit_do;
  [auto 100 with specsplit| |].

(* This is the lemma that justifies the specapply tactic. Executing specapply
   will essentially just bring the goal and rule to the form required by this
   lemma and then apply it. *)
Lemma safe_safe_ro C C' S S' R R' P P' RP:
  C' |-- (S' -->> safe @ P') <@ R' ->
  C |-- C' ->
  P |-- P' ** RP /\ R |-- R' ** ltrue ->
  C |-- (S -->> S' @ RP) <@ R ->
  C |-- (S -->> safe @ P) <@ R.
Proof.
  move=> Hlem HC [HP HR] Hobl. rewrite <-HC in Hlem => {HC}.
  rewrite ->HP => {HP}. lforwardR Hlem.
  - apply spec_reads_frame with (R:=ltrue).
  rewrite ->spec_reads_merge in Hlem. rewrite <-HR in Hlem => {HR}.
  etransitivity; [by apply landR|].
  rewrite ->Hobl at 1. rewrite ->Hlem. clear.
  rewrite -spec_reads_and. cancel2. apply: limplAdj.
  rewrite landA. apply limplL; first exact: landL2.
  rewrite -landA. apply: landL1.
  rewrite landC. apply: landAdj.
  etransitivity; [apply (spec_frame RP)|].
  autorewrite with push_at. reflexivity.
Qed.

Lemma lforallE_spec A (S':spec) S a:
  S' |-- Forall x:A, S x ->
  S' |-- S a.
Proof. move=> H. rewrite ->H. by apply lforallL with a. Qed.

Lemma spec_evars (S S': spec) : S |-- S' -> S |-- S'.
Proof. apply. Qed.

(* This tactic attempts to instantiate universals in a hypothesis with evars.
   It only catches top-level ones, so unfortunately it does not work on, e.g.,
   |-- (Forall x, S x) @ R. *)
Ltac eforalls H :=
  try match type_of H with
  | forall _:_, _ => eapply spec_evars in H
  end; [
    repeat match type_of H with
    | _ |-- Forall _: _, _ => eapply lforallE_spec in H
    end
  | .. ].

(* This tactic works on the conjunctive premise of safe_safe_ro.
   To get the evars instantiated in the correct order when we later run the
   ssimpl tactic, we look ahead a bit and instantiate the instruction pointer
   first. This tactic will look for EIP deep inside the current state and
   instantiate the evar we expect to find for EIP in the precondition of the
   rule we applied with safe_safe_ro. With that done, the code can be picked
   out of the assertion about program memory, which will instantiate all the
   other evars and leave a closed goal.
   This tactic is quite dumb and will do the wrong thing on a sophisticated
   assertion where EIP appears, for example, on the left of a magic wand. But
   in practice, EIP is treated very schematically. *)
Ltac solve_code :=
  match goal with
    |- ?P |-- ?Q /\ _ =>
      match P with context [EIP ~= ?eip] =>
        match Q with context [EIP ~= ?evar] =>
          unify eip evar
        end
      end
  end;
  split; [|by ssimpl]; instantiate.

Module SpecApply.

  (* This is basically a spine of unary operators ending in t_safe. *)
  Inductive term :=
  | t_safe
  | t_impl (S: spec) (t: term)
  | t_at (t: term) (R: SPred)
  | t_atro (t: term) (R: SPred)
  .

  Fixpoint eval t :=
    match t with
    | t_safe => safe
    | t_impl S' t => S' -->> eval t
    | t_at t R => eval t @ R
    | t_atro t R => eval t <@ R
    end.

  (* A spec in normal form: (S -->> safe @ P) <@ R.
     When the spec is None, it means ltrue, and when a SPred is None, it means
     empSP. *)
  Inductive nf := mknf (nfS: option spec) (nfP nfR: option SPred).

  Definition oimpl (So: option spec) (S: spec) :=
    if So is Some S' then S' -->> S else S.

  Definition oconj (S: spec) (So: option spec) :=
    if So is Some S' then S //\\ S' else S.

  Definition osep (Po: option SPred) (P: SPred) :=
    if Po is Some P' then P' ** P else P.

  Definition oat (So: option spec) (R: SPred) : option spec :=
    if So is Some S' then Some (S' @ R) else None.

  (* To normal form.
     If the term is equivalent to a normal form, it computes that. This may
     involve distributing "@"'s over other connectives or decurrying
     implications.
     The option types in the normal form are used here for two purposes. First,
     a normal form only exists if no "<@" is nested within an implication or
     another "<@". We need to reflect on whether a proper read-only frame has
     been encountered yet, which the option will tell us. Second, it is used to
     avoid things like S1 //\\ ... //\\ Sn //\\ ltrue by allowing us to see if
     there are any proper elements left to be conjoined.
   *)
  Fixpoint tonf (t: term) : option nf :=
    match t with
    | t_safe => Some (mknf None None None)
    | t_impl S' t =>
        match tonf t with
        | Some (mknf So Po None) => Some (mknf (Some (oconj S' So)) Po None)
        | _ => None
        end
    | t_at t R =>
        match tonf t with
        | Some (mknf So Po Ro) => Some (mknf (oat So R) (Some (osep Po R)) Ro)
        | None => None
        end
    | t_atro t R =>
        match tonf t with
        | Some (mknf So Po None) => Some (mknf So Po (Some R))
        (* If there's more than one t_atro, we do not attempt to merge them.
           This would require the spec_reads_split lemma, whose side condition
           we cannot deal with at this point. *)
        | _ => None
        end
    end.

  Definition eval_ospec (So: option spec) :=
    if So is Some S' then S' else ltrue.

  Definition eval_oSPred (Po: option SPred) :=
    if Po is Some P' then P' else empSP.

  Definition eval_nf (spr: nf) :=
    let: mknf So Po Ro := spr in
    (eval_ospec So -->> safe @ eval_oSPred Po) <@ eval_oSPred Ro.

  Lemma limpltrue (P: spec): ltrue -->> P -|- P.
  Proof.
    split.
    - etransitivity; [apply landR; [reflexivity|apply ltrueR] |].
      apply: landAdj. reflexivity.
    - apply: limplAdj. exact: landL1.
  Qed.

  Lemma limplcurry (P Q R: spec): P //\\ Q -->> R -|- P -->> Q -->> R.
  Proof.
    split.
    - apply: limplAdj. apply: limplAdj. rewrite landA. exact: landAdj.
    - apply: limplAdj. apply: limplL; first exact: landL1.
      apply: limplL; first exact: landL2. exact: landL1.
  Qed.

  Lemma oimpl_correct So S : oimpl So S -|- eval_ospec So -->> S.
  Proof. case: So => [So|] //=. by rewrite limpltrue. Qed.

  Lemma oconj_correct S So : oconj S So -|- S //\\ eval_ospec So.
  Proof. case: So => [So|] //=. split; [exact: landR | exact: landL1]. Qed.

  Lemma osep_correct Po P : osep Po P -|- eval_oSPred Po ** P.
  Proof. case: Po => [Po|] //=. by rewrite empSPL. Qed.

  Lemma oat_correct So R : eval_ospec (oat So R) -|- eval_ospec So @ R.
  Proof. case: So => [So|] //=. by autorewrite with push_at. Qed.

  Lemma tonf_correct t spr:
    tonf t = Some spr ->
    eval_nf spr -|- eval t.
  Proof.
    elim: t spr => [ | S t IH | t IH R | t IH R ] spr Hoc.
    - move: Hoc => [<-] /=. rewrite spec_reads_eq_at !spec_at_emp.
      by rewrite limpltrue.
    - simpl in Hoc. destruct (tonf t) as [[So Po [R|]]|] => //.
      move: Hoc => [<-]. rewrite /eval_nf.
      rewrite /eval_ospec /eval -/eval. rewrite -IH; [|reflexivity].
      rewrite /eval_nf. rewrite !spec_reads_eq_at !spec_at_emp.
      by rewrite oconj_correct limplcurry.
    - simpl in Hoc. destruct (tonf t) as [[So Po Ro]|] => //.
      move: Hoc => [<-]. rewrite /eval_nf.
      rewrite oat_correct /eval -/eval.
      rewrite -IH; [|reflexivity]. rewrite /eval_nf.
      autorewrite with push_at. rewrite [eval_oSPred (Some _)]/eval_oSPred.
      by rewrite osep_correct.
    - simpl in Hoc. destruct (tonf t) as [[So Po [R'|]]|] => //.
      move: Hoc => [<-]. rewrite /eval_nf.
      rewrite /eval -/eval. rewrite -IH; [|reflexivity].
      rewrite /eval_nf. rewrite !spec_reads_eq_at !spec_at_emp.
      reflexivity.
  Qed.

  Ltac quote_term S :=
    match S with
    | safe => constr:t_safe
    | ?S1 -->> ?S2 => let t2 := quote_term S2 in constr:(t_impl S1 t2)
    | ?S @ ?R => let t := quote_term S in constr:(t_at t R)
    | ?S <@ ?R => let t := quote_term S in constr:(t_atro t R)
    end.

  (* A version of safe_safe_ro that works on reflected specs. *)
  Lemma safe_safe_nf t t' C C' RP:
    match tonf t , tonf t' with
    | Some (mknf So Po Ro) , Some (mknf So' Po' Ro') =>
        C' |-- eval t' ->
        C |-- C' ->
        eval_oSPred Po |-- osep Po' RP /\
        eval_oSPred Ro |-- osep Ro' ltrue ->
        C |-- oimpl So (eval_ospec So' @ RP) <@ eval_oSPred Ro ->
        C |-- eval t
    | _ , _ => True
    end.
  Proof.
    case Ht: (tonf t) => [[So Po Ro]|] //.
    case Ht': (tonf t') => [[So' Po' Ro']|] //.
    rewrite -tonf_correct; last apply Ht'.
    rewrite -tonf_correct; last apply Ht.
    rewrite /eval_nf !osep_correct oimpl_correct. apply safe_safe_ro.
  Qed.

  (* Create hint database by putting a dummy entry in it. *)
  Hint Unfold not : specapply.

  Ltac specapply lem :=
    let Hlem := fresh in
    (* Move the lemma to be applied into the context so we can preprocess it
       from there. *)
    move: (lem) => Hlem;
    (* Unfold definitions as needed to expose a [safe]. Wrappers around [safe]
       should be added to the specapply db with Hint Unfold. *)
    autounfold with specapply in Hlem;
    (* Instantiate binders with evars so we can reflect the hypothesis. *)
    eforalls Hlem; [
      match type_of Hlem with ?C' |-- ?S' =>
        let tlem := quote_term S' in
        match goal with |- ?C |-- ?S =>
          let tgoal := quote_term S in
          (* Apply safe_safe_nf, which will match if tgoal and tlem could be
             put into normal form. The first subgoal is the lemma to be
             applied, the second subgoal is (C |-- C'), which is often trivial,
             the third premise is a conjunction of assertion-logic entailments,
             and the last premise is the goal that's left after doing this
             application. *)
          eapply (@safe_safe_nf tgoal tlem C C'); [exact Hlem | try done | |];
          cbv [eval_ospec eval_oSPred osep oconj oimpl oat];
          [.. | try solve_code |]
        end
      end
    | .. ];
    clear Hlem.

  (*
  Example dummy (S1 S2: spec) (P1 P2 R1 R2: SPred):
    |-- (S1 -->> safe @ P1) <@ R1 ->
    |-- (S2 -->> safe @ P2) <@ R2.
  Proof.
    move=> H. specapply H.
  *)

  (*
  Example dummy (S1 S2: spec) (P1 P2 R1 R2: SPred): True.
  Eval simpl in
    if (tonf (t_atro (t_impl S1 (t_at (t_impl S2 (t_at t_safe P1)) P2)) R1))
    is Some spr then eval_nf spr else lfalse.
  done. Qed.
  *)

End SpecApply.

Ltac specapply := SpecApply.specapply.
