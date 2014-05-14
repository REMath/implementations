Require Import ssreflect ssrbool ssrnat eqtype seq fintype.
Require Import procstate procstatemonad bitsops bitsprops bitsopsprops.
Require Import SPred septac spec spectac safe basic program.
Require Import instr instrsyntax decinstr instrrules reader pointsto cursor basic macros.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope instr_scope.

Definition xorSwapImpl (r1 r2: Reg) : program :=
  XOR r1, r2;;
  XOR r2, r1;;
  XOR r1, r2.

Definition tmpSwapImpl (r1 r2 rt: Reg) : program :=
  MOV rt, r1;;
  MOV r1, r2;;
  MOV r2, rt.

(* Spec that is "common" between the two implementations *)
(* We use "@" to conjoin implementation-specific scratch usage *)
Definition basicSwap (r1 r2: Reg) c := 
  Forall v, Forall w, 
  basic 
  (r1 ~= v ** r2 ~= w) 
  c 
  (r1 ~= w ** r2 ~= v).

Lemma xorSwapCorrect (r1 r2: Reg) : 
  |-- basicSwap r1 r2 (xorSwapImpl r1 r2) @ OSZCP_Any.
Proof. 
  rewrite /xorSwapImpl/basicSwap. specintros => v w. autorewrite with push_at.

  (* XOR r1, r2 *)
  basicapply XOR_RR_rule. 

  (* XOR r2, r1 *)
  basicapply XOR_RR_rule; rewrite /OSZCP_Any/OSZCP/flagAny; sbazooka.

  (* XOR r1, r2 *)
  basicapply XOR_RR_rule; rewrite /OSZCP_Any/OSZCP/flagAny; sbazooka.

  (* Now we're left reasoning about XOR *)  
  rewrite {2}[X in xorB w X]xorBC. 
  rewrite [X in r2~=X]xorBA.
  autorewrite with bitsHints.  
  rewrite [X in xorB _ X]xorBC xorBA. 
  autorewrite with bitsHints. 
  by ssimpl. 
Qed. 

Lemma tmpSwapCorrect (r1 r2 rt: Reg) : 
  |-- basicSwap r1 r2 (tmpSwapImpl r1 r2 rt) @ rt?. 
Proof. 
  rewrite /tmpSwapImpl/basicSwap. specintros => v w. autorewrite with push_at. 

  (* MOV rt, r1 *)
  basicapply MOV_RR_rule.

  (* MOV r1, r2 *)
  basicapply MOV_RR_rule; rewrite /regAny; sbazooka.
 
  (* MOV r2, r1 *)
  basicapply MOV_RR_rule; rewrite /regAny; sbazooka.
Qed. 

