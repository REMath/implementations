(*===========================================================================
  Implementation of "Game of Life"
  ===========================================================================*)
Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq fintype tuple.
Require Import procstate procstatemonad bitsrep bitsops bitsprops bitsopsprops.
Require Import SPred septac spec safe basic program macros call.
Require Import instr instrsyntax decinstr instrrules reader pointsto cursor screenspec.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope instr_scope.

(* Compute line position EDX in screen buffer starting at EDI *)
(* EDI contains the position; EDX is preserved if it is in range *)
Definition inlineComputeLinePos: program :=
     SHL EDX, 5;;
     ADD EDI, EDX;;
     SHL EDX, 2;;
     ADD EDI, EDX;;
     SHR EDX, 7.

Definition inlineComputeLine_spec (row:nat) (base:DWORD) (instrs: program) :=
  basic (EDX ~= #row ** EDI ~= base) instrs
        (EDX ~= #row ** EDI ~= base +# row*160) @ OSZCP_Any.

Lemma inlineComputeLinePos_correct row base :
  row < numRows -> 
  |-- inlineComputeLine_spec row base inlineComputeLinePos. 
Proof. 
  move => NR. 
  rewrite /inlineComputeLine_spec/inlineComputeLinePos.
  autorewrite with push_at. 

  (* We don't unfold OSZCP_Any anywhere because no rules talk about flags *)

  (* SHL EDX, 5 *)
  basicapply SHL_RI_rule => //.  

  (* ADD EDI, EDX *)
  basicapply ADD_RR_ruleNoFlags.

  (* SHL EDX, 2 *)
  basicapply SHL_RI_rule => //.

  (* ADD EDI, EDX *)
  basicapply ADD_RR_ruleNoFlags. 

  (* SHR EDX, 7 *)
  basicapply SHR_RI_rule => //. 

  rewrite /iter. autorewrite with bitsHints. (*rewrite -addB_addn. rewrite !shlB_asMul. *)
  do 6 rewrite -[in X in EDI~=X]mulB_muln. 
  rewrite !fromNat_mulBn. 
  replace (2 * _) with 32 => //. 
  replace (32 * (2*2)) with 128 => //. 
  rewrite -addB_addn. 
  (* Can't use ring 'cos it's inside bits *)
  rewrite -mulnDr addnC. replace (128 + 32) with 160 => //.
  ssimpl. 

  rewrite -6!mulnA. 
  replace (2 * _) with (2^7) => //.  
  have SH := @shrB_mul2exp 7 25 #row. 
  rewrite /iter fromNat_mulBn in SH. rewrite SH {SH}. 
  reflexivity.
  rewrite toNat_fromNatBounded. apply (ltn_trans NR) => //.  
  apply (ltn_trans NR) => //. 
Qed.   

(* Increment ESI if location buf[ECX, EDX] contains a dot *)
Definition incIfDot buf: program :=
  LOCAL skip;
  MOV EDI, buf;;
  inlineComputeLinePos;;
  CMP BYTE [EDI + ECX*2], #c"*";;
  JNE skip;;
  INC ESI;;
skip:;. 

Definition decModN (r:Reg) n : program :=
  CMP r, 0;;
  ifthenelse CC_Z true (MOV r, (n.-1)) (DEC r).

Definition incModN (r: Reg) n : program :=
  CMP r, (n.-1);;
  ifthenelse CC_Z true (MOV r, 0) (INC r).

Require Import div.
Lemma decModN_correct (r:Reg) n m : n < 2^32 -> m < n ->
  |-- basic (r ~= #m) (decModN r n) (r ~= #((m + n.-1) %% n)) @ OSZCP_Any.
Proof.
  move => LT1 LT2. 

  autorewrite with push_at.   
  rewrite /decModN.

  (* CMP r, 0 *)
  basicapply CMP_RI_eq_rule.
  
  apply: basic_roc_pre;
  last apply (if_rule 
    (P:= fun b => 
    (m == 0) = b /\\ r ~= #m ** flagAny OF ** flagAny SF ** flagAny CF ** flagAny PF)). 

  rewrite /ConditionIs. sbazooka.
 
  apply fromNatBounded_eq => //. 
  by apply (ltn_trans LT2). 

  specintros => /eqP->. 
  basicapply MOV_RI_rule. rewrite /regAny; sbazooka.
  rewrite /OSZCP_Any. rewrite /ConditionIs/flagAny. rewrite add0n modn_small. 
  sbazooka.
  destruct n => //. 

  simpl (~~ _). specintros => H. 
  basicapply DEC_R_ruleNoFlags. 
  rewrite /OSZCP_Any/ConditionIs/flagAny. sbazooka.
  destruct m => //. 
  rewrite decB_fromSuccNat. 
  destruct n => //. rewrite succnK. rewrite addSnnS. rewrite modnDr. 
  rewrite modn_small => //. 
  sbazooka. 
  apply (leq_ltn_trans (leq_pred _) LT2). 
Qed. 

Definition incModN_correct (r:Reg) n m : n < 2^32 -> m < n ->
  |-- basic (r ~= #m) (incModN r n) (r ~= #((m.+1) %% n)) @ OSZCP_Any.
Proof.
move => LT1 LT2. 

  autorewrite with push_at.   
  rewrite /incModN.

  (* CMP r, 0 *)
  basicapply CMP_RI_eq_rule.

  apply: basic_roc_pre;
  last apply (if_rule 
    (P:= fun b => 
    (m == n.-1) = b /\\ r ~= #m ** flagAny OF ** flagAny SF ** flagAny CF ** flagAny PF)). 

  rewrite /ConditionIs. sbazooka.
  have B2: m < 2^32. 
  by apply (ltn_trans LT2).  
  apply fromNatBounded_eq => //. 

  by apply (leq_ltn_trans (leq_pred _)). 

  specintros => /eqP->. 
  basicapply MOV_RI_rule. rewrite /regAny. sbazooka.
  rewrite /OSZCP_Any. rewrite /ConditionIs. rewrite /flagAny. 
  rewrite (ltn_predK LT2). sbazooka. by rewrite modnn. 

  simpl (~~ _). specintros => H. 
  basicapply  INC_R_ruleNoFlags. 
  rewrite /OSZCP_Any/ConditionIs/flagAny. sbazooka.
  sbazooka. 
  rewrite incB_fromNat. rewrite modn_small => //.
  rewrite ltn_neqAle. rewrite LT2 andbT. 
  rewrite -eqSS in H. rewrite prednK in H. by rewrite H. 
  by destruct n. 
Qed. 

(* Move ECX one column left, wrapping around if necessary *)
Definition goLeft: program := decModN ECX numCols.

Lemma goLeftCorrect col : col < numCols ->
  |-- basic (ECX ~= # col) goLeft (ECX ~= #((col + numCols.-1) %% numCols))@ OSZCP_Any.
Proof. apply decModN_correct => //. Qed.

(* Move ECX one column right, wrapping around if necessary *)
Definition goRight: program := incModN ECX numCols. 

Lemma goRightCorrect col : col < numCols ->
  |-- basic (ECX ~= # col) goRight (ECX ~= #((col.+1) %% numCols)) @ OSZCP_Any.
Proof. apply incModN_correct => //. Qed.

(* Move EDX one row up, wrapping around if necessary *)
Definition goUp: program := decModN EDX numRows.

Lemma goUpCorrect row : row < numRows ->
  |-- basic (EDX ~= # row) goUp (EDX ~= #((row + numRows.-1) %% numRows)) @ OSZCP_Any.
Proof. apply decModN_correct => //. Qed.

(* Move EDX one row down, wrapping around if necessary *)
Definition goDown: program := incModN EDX numRows.

Lemma goDownCorrect row : row < numRows ->
  |-- basic (EDX ~= # row) goDown (EDX ~= #((row.+1) %% numRows)) @ OSZCP_Any.
Proof. apply incModN_correct => //. Qed.

(* Given a character at buf[ECX, EDX], return its neighbour count in ESI *)
(* Preserve ECX, EDX *)
Definition countNeighbours (buf:DWORD) : program := 
  let_toyfun f := incIfDot buf
  in
  MOV ESI, 0;;
  goLeft;; call_toyfun f;;
  goUp;; call_toyfun f;;
  goRight;; call_toyfun f;;
  goRight;; call_toyfun f;;
  goDown;; call_toyfun f;;
  goDown;; call_toyfun f;;
  goLeft;; call_toyfun f;;
  goLeft;; call_toyfun f;;
  goUp;; goRight.

Definition bufDefined (buf:DWORD) := memAny buf (buf +# numRows*numCols*2).

Definition writeChar buf ch: program :=
  MOV EDI, buf;;
  inlineComputeLinePos;; 
  MOV BYTE [EDI+ECX*2], charToBYTE ch.

(* Using the screen buffer as input, produce new chracter in buf *)
Open Scope char_scope.
Definition oneStep screen buf: program :=
  LOCAL ALIVE;
  LOCAL SKIP;
  LOCAL KILL;
  countNeighbours screen;;
  MOV EDI, screen;;  
  inlineComputeLinePos;;
  CMP BYTE [EDI+ECX*2], #c"*";;
  JE ALIVE;;
  CMP ESI, 3;;
  JNE SKIP;;
  writeChar buf ("*":Ascii.ascii);;
  JMP SKIP;;
ALIVE:;;
  CMP ESI, 3;;
  JG KILL;;
  CMP ESI, 2;;
  JL KILL;;
  JMP SKIP;;
KILL:;;
  writeChar buf " ";;
SKIP:;.
 
(* Code for clear screen. *)
Definition clearColour := toNat (n:=8) (#x"4F").

Definition clsProg :program := 
      MOV EBX, screenBase;; 
      while (CMP EBX, screenLimit) CC_B true ( (* while EBX < screenLimit *)
        MOV BYTE [EBX], #c" ";; 
        MOV BYTE [EBX+1], # clearColour;;
        INC EBX;; INC EBX (* move one character right on the screen *) 
      ).

Definition oneStepScreen screen buf :program := 
      MOV EDX, 0;;
      while (CMP EDX, numRows) CC_B true ( (* while EDX < numRows *)
        MOV ECX, 0;; 
        while (CMP ECX, numCols) CC_B true ( (* while ECX < numCols *)
          oneStep screen buf;;
          INC ECX
        );;
        INC EDX
      ).

(* Copy the screen to a buffer, or vice versa.
   Only copy the text, not the colours *)
Definition copyBuf (src dst:DWORD) : program:=
      MOV ESI, src;;
      MOV EDI, dst;;
      while (CMP ESI, (src +# numCols*numRows.*2:DWORD)) CC_B true ( (* while ESI < screenLimit *)
        MOV EAX, [ESI];; 
        MOV [EDI], EAX;;
        ADD ESI, 4;; ADD EDI, 4
      ).

Definition delay:program := 
      MOV EBX, (#x"08000001": DWORD);;
      while (CMP EBX, 0) CC_Z false (DEC EBX).


Definition copyBlock (src dst:DWORD) : program:=
      MOV ESI, src;;
      MOV EDI, dst;;
      while (CMP ESI, (src +# numCols*numRows.*2:DWORD)) CC_B true ( (* while ESI < screenLimit *)
        MOV EAX, [ESI];; 
        MOV [EDI], EAX;;
        ADD ESI, 4;; ADD EDI, 4
      ).


Fixpoint makeLine s (screen:DWORD) :=
  if s is String c s' 
  then writeChar screen c;; goRight;; makeLine s' screen
  else prog_skip. 

Fixpoint makeFigure ss screen :=
  if ss is s::ss' 
  then MOV EAX, ECX;; makeLine s screen;; MOV ECX, EAX;; goDown;; makeFigure ss' screen
  else prog_skip.  

(*
Definition makeFigureAlt (ss: seq string) screen render :=
LOCAL shape;
  MOV EDX, (fromNat (List.length ss):DWORD);;
  MOV ECX, (fromNat (String.length (List.hd ""%string ss)):DWORD);;
  MOV EDI, screen;;
  CALL render;;
shape: 
  ds (flatten ss).
*)

Open Scope string.
Definition makeGlider := makeFigure
  [:: " * ";
      "  *";
      "***"].

Definition makeBlock := makeFigure
  [:: "**";
      "**"].

Definition makeBeehive := makeFigure 
  [:: " ** ";
      "*  *";
      " ** "].

Definition makeBeacon := makeFigure
  [:: "**  ";
      "**  ";
      "  **";
      "  **"].

Definition makePulsar := makeFigure
  [:: "  ***   ***  ";
      "             ";
      "*    * *    *";
      "*    * *    *";
      "*    * *    *";
      "  ***   ***  ";
      "             ";
      "  ***   ***  ";
      "*    * *    *";
      "*    * *    *";
      "*    * *    *";
      "             ";
      "  ***   ***  "].
  
  
