Require Import ssreflect ssrfun ssrbool finfun fintype ssrnat eqtype seq tuple.
Require Import procstate procstatemonad bitsrep bitsops bitsprops bitsopsprops.
Require Import SPred septac spec safe basic program macros call.
Require Import instr monad reader writer procstate procstatemonad mem exn eval decinstr
               monadinst ioaction bitsrep bitsops eval step encinstr pointsto cursor.
Require Import program programassem reg instrsyntax instrrules.
Require Import spectac iltac triple.

Require Import stringbuff.
Require Import compiler.

(* ATBR *)
Require Import ATBR.DecideKleeneAlgebra.
Require Import ATBR.DKA_Definitions.



(****************************************************************)
(* Interface with RelationAlgebra                               *)
(****************************************************************)

Section Compile.

Variables
  (r: regex)
  (alphabet: seq DWORD)
  (nz_alpha: CString alphabet).

Variables 
  (acc rej err: DWORD).

Require Import BinNums BinPos.

Definition to_pos (n: DWORD) : positive :=
 Pos.of_nat (toNat n).

(*
Compute (to_pos #0).
Compute (to_pos #1).
Compute (to_pos #2).
*)

Definition from_pos (p: positive): DWORD :=
  # (Pos.to_nat p).

(*
Compute (toHex (from_pos (to_pos #0))).
Compute (toHex (from_pos (to_pos #1))).
Compute (toHex (from_pos (to_pos #2))).
*)

(*
Lemma equiv (m n: nat): ordinal.ltb m n = (m < n).
Proof.
  rewrite /leq.
  elim: m n => [|m IH] n /=.
  * (* CASE: m = 0 *)
    by case n => //.
  * (* CASE: m = suc m *)
    case n=> //.
Qed.

Definition to_I (n: nat) (o: ordinal.ord n) : 'I_n.
move: o=> [x leqxn].
apply Ordinal with (m := x).
rewrite equiv in leqxn.
rewrite leqxn //.
Defined.

(* Compute (to_I (n := 4) (ordinal.ordS (ordinal.ordS ordinal.ord0))). *)

Definition from_I (n: nat) (o: 'I_n): ordinal.ord n.
move: o => [m leqmn].
apply (ordinal.Ord m).
rewrite -leqmn.
exact: equiv.
Defined.
*)
(* Compute (ordinal.nat_of_ord (from_I (n := 4) (ordS ord0))). *)

(*
Definition alphabetPos := [seq to_pos a | a <- alphabet].
*)
Definition dfa_r: DFA.t := X_to_DFA r.

(*
Compute (X_to_DFA (RegExp.var 1)).
*)

Definition dfa_size: nat := Pos.to_nat (DFA.size dfa_r).

Lemma init_to_ord: Pos.to_nat (DFA.initial dfa_r) < dfa_size.
Proof.
  have dfa_br: DFA.bounded dfa_r by apply X_to_DFA_bounded.
  rewrite /dfa_size.
  have: (Pos.to_nat (DFA.initial dfa_r) < Pos.to_nat (DFA.size dfa_r))%coq_nat
    by rewrite -Pnat.Pos2Nat.inj_lt;
       apply (DFA.bounded_initial dfa_br).
  move/leP=> //=.
Qed.



Definition dfa_init: 'I_dfa_size.
apply (Ordinal (m := (Pos.to_nat (DFA.initial dfa_r)))).
apply init_to_ord.
Defined.


Definition accept (s: 'I_dfa_size): bool := StateSet.mem (nat_of_ord s) (DFA.finaux dfa_r).

(*Definition accept (s: 'I_dfa_size): bool := dfa.v dfa_r (from_I s).*)

Lemma trans_to_ord v s : Pos.to_nat (DFA.delta dfa_r (to_pos v) s) < dfa_size.
Proof.
  have dfa_br: DFA.bounded dfa_r 
    by apply X_to_DFA_bounded.
  rewrite /dfa_size.

apply/ltP.
rewrite -Pnat.Pos2Nat.inj_lt.
apply (DFA.bounded_delta dfa_br).
Qed.


Definition trans (s: 'I_dfa_size)(v: DWORD): 'I_dfa_size.
  apply (Ordinal (m := Pos.to_nat (DFA.delta dfa_r (to_pos v) (nat_of_ord s)))).
  apply trans_to_ord.
Defined.
(*Definition trans (s: 'I_dfa_size)(v: DWORD): 'I_dfa_size :=
  to_I (dfa.M dfa_r (from_I s) (to_pos v)).*)

Definition code: program := compiler acc rej err dfa_init alphabet accept trans.

End Compile.


