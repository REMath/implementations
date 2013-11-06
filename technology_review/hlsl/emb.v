Require Import ssreflect ssrfun ssrnat ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Set Printing Implicit Defensive.
Set Transparent Obligations.

(*======================================================================================
  Embeddings
  ======================================================================================*)
Class EMB t s := PEmb
{ inj: t -> s; inv: s -> option t; 
  injinv : pcancel inj inv
}.

Notation "i ^-1" := (inv i). 
Coercion inj : EMB >-> Funclass.

Definition Emb t s (inj: t -> s) inv (c: cancel inj inv) := PEmb (can_pcan c).

(* The map of an embedding is injective *)
Lemma embInj {a b} : forall (i : EMB a b) x y, i x = i y -> x = y. 
Proof. move => emb x y H. apply: pcan_inj H. apply injinv. Qed. 

(* Compose two embeddings (transitivity) *)
Definition seqE {a b c} (i1: EMB a b) (i2: EMB b c) := 
  PEmb (pcan_pcomp injinv injinv).

Definition prodE {a b c d} (i1: EMB a b) (i2: EMB c d) : EMB (a*c) (b*d).
refine (@PEmb _ _ (fun x => (i1 x.1, i2 x.2)) 
  (fun y => if inv y.1 is Some x1 then 
            if inv y.2 is Some x2 then Some (x1,x2) else None else None) _). 
move => [z1 z2]. by rewrite !injinv.
Defined. 

Lemma uniqueSingleton t (emb : EMB t unit) : forall x, inv tt = Some x.
Proof. move => x. assert (H := injinv x). by destruct (emb x). Qed. 

