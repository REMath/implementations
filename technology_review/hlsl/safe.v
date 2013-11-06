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
Transparent ILPre_Ops.

Program Definition safe := mkspec (fun k P =>
    forall s: ProcState, (P ** ltrue) (toPState s) ->
    exists s',
    doMany k step s = Success _ (s',tt)
  ) _ _.
Next Obligation.
  move=> k.
  have ->: k.+1 = (k + 1)%coq_nat by omega.
  move => P Hsafe s Hs.
  have [s'' Hs''] := Hsafe s Hs. move: Hs''.
  rewrite doManyAdd /=.
  case: (doMany k step s) => [|[s' u] Hs']; first by discriminate.
  case: u. by exists s'.
Qed.
Next Obligation.
  move=> k P P' [R HR] Hsafe s Hs. 
  edestruct (Hsafe s); last by eauto.
  rewrite ->lentails_eq in Hs. rewrite <-HR in Hs.
  rewrite lentails_eq. rewrite ->Hs. by ssimpl.
Qed.

Instance AtEx_safe: AtEx safe.
Proof.
  move=> A f. move=> k P Hf.
  unfold safe, spec_at, mkspec, spec_fun, ILPreFrm_pred in *.
  simpl in Hf. move=> s Hs. sdestruct: Hs => x Hs.
  edestruct Hf; [eassumption|]. eauto.
Qed.

Instance AtContra_safe: AtContra safe.
Proof.
  move=> R R' HR. move=> k P HP.
  unfold safe, spec_at, mkspec, spec_fun, ILPreFrm_pred in *.
  move=> s Hs. apply HP.
  rewrite lentails_eq. rewrite <-HR. by rewrite -lentails_eq.
Qed.

