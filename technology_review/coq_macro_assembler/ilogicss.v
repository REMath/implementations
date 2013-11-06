Require Import ssreflect ssrfun ssrbool eqtype fintype finfun seq tuple.
Require Import ilogic.

(* Importing this file really only makes sense if you also import ilogic, so we
   force that. *)
Require Export ilogic bilogic.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import FunctionalExtensionality. 


(* This should not be here, //Jesper *)

Section ILogicSSReflect.
  Context {A} `{ILogic A}.

  Lemma lpropandT P : true /\\ P -|- P. 
  Proof. rewrite /lpropand. split; [by apply lexistsL | by apply lexistsR]. Qed. 

  Lemma lpropandF P : false /\\ P -|- lfalse. 
  Proof. rewrite /lpropand. split; [by apply lexistsL | done]. Qed.

End ILogicSSReflect.

(* Tactics for doing forward reasoning from a hypothesis. *)
Lemma lforwardR {Frm} `{IL: ILogic Frm} P Q R:
  Q |-- R -> P |-- Q -> P |-- R.
Proof. intros; etransitivity; eassumption. Qed.
Tactic Notation "lforwardR" hyp(H) := eapply lforwardR in H; last first.

Lemma lforwardL {Frm} `{IL: ILogic Frm} P Q R:
  P |-- Q -> Q |-- R -> P |-- R.
Proof. intros; etransitivity; eassumption. Qed.
Tactic Notation "lforwardL" hyp(H) := eapply lforwardL in H; last first.

(* This tactic is a ilogic version of [move:]. Can it be done easier? *)
Ltac lrevert x :=
  move: x;
  match goal with
  | |- ?P -> _ |-- ?G =>
      move=> x;
      transitivity (P ->> G);
      [clear x | apply lpropimplL; [exact x|reflexivity] ]
  | |- forall a, _ |-- @?G a =>
      move=> x;
      transitivity (lforall G);
      [clear x | apply lforallL with x; reflexivity ]
  end.
