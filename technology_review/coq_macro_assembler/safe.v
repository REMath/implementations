(*===========================================================================
    "safe" predicate
  ===========================================================================*)
Require Import ssreflect ssrbool ssrfun ssrnat eqtype tuple seq fintype.
Require Import bitsrep procstate procstatemonad SPred septac spec.
Require Import instr eval monad monadinst reader pointsto step cursor.
Require Import triple (* for toPState *).

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Setoid RelationClasses Morphisms.
Local Obligation Tactic := idtac.

Program Definition safe := mkspec (fun k P =>
    forall s: ProcState, (P ** ltrue) (toPState s) ->
    exists s', exists o, 
    doMany k step s = (o, Success _ (s',tt))
  ) _ _.
Next Obligation.
  move=> k.
  have ->: k.+1 = (k + 1)%coq_nat by omega.
  move => P Hsafe s Hs.
  have [s'' [o'' Hs'']] := Hsafe s Hs. move: Hs''.
  rewrite doManyAdd /=. 
  case: (doMany k step s) => [o' u]. 
  case: u => //. elim => [s' u]. exists s'. exists o'. by destruct u. 
Qed.
Next Obligation.
  move=> k P P' [R HR] Hsafe s Hs. 
  edestruct (Hsafe s); last by eauto.
  rewrite ->lentails_eq in Hs. rewrite <-HR in Hs.
  rewrite lentails_eq. rewrite ->Hs. by ssimpl.
Qed.

Transparent ILPre_Ops.
Instance AtEx_safe: AtEx safe.
Proof.
  move=> A f. 
  move=> k P Hf.
  unfold safe, spec_at, mkspec, spec_fun in *; simpl in *.
  move=> s Hs.
  sdestruct: Hs => a Hs.
  eapply Hf; eassumption.
Qed.

Instance AtContra_safe: AtContra safe.
Proof.
  move=> R R' HR. move=> k P HP.
  unfold safe, spec_at, mkspec, spec_fun, ILPreFrm_pred in *.
  move=> s Hs. apply HP.
  rewrite lentails_eq. rewrite <-HR. by rewrite -lentails_eq.
Qed.

