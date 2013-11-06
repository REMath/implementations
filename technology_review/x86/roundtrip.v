Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq tuple fintype finfun.
Require Import bitsrep bitsprops bitsops reg instr mem encdechelp monad codec 
               reader enc encinstr decinstr emb cursor.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Ltac unfoldDM := (let DM := fresh in set DM:= decMap _; hnf in DM; rewrite /DM {DM}).

Ltac simpEq :=
    repeat (match goal with |- context [?XX == ?YY] => 
      (try change (XX == YY) with false; try change (XX == YY) with true) end); cbv iota.
(*try replace (_ == _) with false by done;
        try replace (_ == _) with true by done).  *)

Lemma encodeNonSP : forall (r:NonSPReg), (encReg r == #b"100") = false.  
Proof. by case. Qed.
 

(* Regbits might be an operand extension (for unary ops) or a register encoding
   (for binary ops) *)
Instance RegMemCodec : Codec BITS3RegMem_readerType.
Proof.
move => m p p' [regbits rm].
simpl getReader. rewrite /readRegMem/encode/encodeRegMem. 
case rm => [r | ms].

(* rm = DstR _ *)
- apply: applyRoundtrip. by rewrite split3app encRegK. 

(* rm = DstM m0 *)
+ case: ms => [base indexAndScale offset] .
  case eq0: (offset == zero _). 

  (******* displacement 0 ********)
  - rewrite fromNat0 (eqP eq0). 
    case: indexAndScale.

  (* Have index and scale *) 
    * move => [ix scale]. 
      apply: applyRoundtripCat => q. 
      rewrite split3app. simpEq. 
      rewrite /readSIB eq_refl assoc. 
      apply: applyRoundtrip. rewrite split3app. 
      by rewrite encNonSPRegK encRegK encScaleK id_l. 

  (* Don't have index and scale *)
    * case: base => [n |].

      (* base is NonSP *)
      apply: applyRoundtrip.  
      rewrite split3app. simpEq. rewrite /readSIB.
      by rewrite (encodeNonSP n) encRegK. 

      (* base is SP *)
      apply: applyRoundtripCat => q. rewrite split3app. 
      rewrite !eq_refl. simpEq. 
      rewrite /readSIB eq_refl. rewrite assoc. 
      by apply: applyRoundtrip. 

  (******* 8-bit or 32-bit displacement ********)
  - case E: (signTruncate _) => [b |]. 

(****** 8-bit displacement *********)
    case: indexAndScale.

    (* Have index and scale *)
    * move => [ix scale].
      apply: applyRoundtripCat => q. 
      rewrite split3app/readSIB. simpEq. 
      rewrite assoc. apply: applyRoundtripCat => ?. 
      rewrite split3app encNonSPRegK encScaleK encRegK id_l. 
      apply: applyRoundtrip.
      by rewrite (signTruncateK E).  

   (* Don't have index and scale *)
    * case: base => [n |]. 

      (* base is NonSP *)
      apply: applyRoundtripCat => ?. rewrite split3app. 
      rewrite /readSIB. simpEq. simpEq. rewrite encodeNonSP id_l encRegK. 
      apply: applyRoundtrip.  
      by rewrite (signTruncateK E). 

      (* base is SP *)
      apply: applyRoundtripCat => ?. rewrite split3app. 
      rewrite /readSIB. simpEq. rewrite assoc. apply: applyRoundtripCat => ?. 
      rewrite split3app. rewrite id_l.  
      apply: applyRoundtrip. 
      by rewrite (signTruncateK E).  

(******* 32-bit displacement ********)
- case: indexAndScale.  

  (* Have index and scale *)
  + move => [ix scale]. 
    apply: applyRoundtripCat => q. 
    rewrite split3app/readSIB. simpEq. 
      rewrite assoc. apply: applyRoundtripCat => ?. 
      rewrite split3app encNonSPRegK encScaleK encRegK id_l. 
      apply: applyRoundtrip.
      done. 

   (* Don't have index and scale *)
    * case: base => [n |]. 

      (* base is NonSP *)
      apply: applyRoundtripCat => ?. rewrite split3app. 
      rewrite /readSIB. simpEq. simpEq. rewrite encodeNonSP id_l encRegK. 
      apply: applyRoundtrip.  
      done.

      (* base is SP *)
      apply: applyRoundtripCat => ?. rewrite split3app. 
      rewrite /readSIB. simpEq. rewrite assoc. apply: applyRoundtripCat => ?. 
      rewrite split3app. rewrite id_l.  
      apply: applyRoundtrip. 
      done. 
Qed.


(* Why oh why can't we just use simpl *)
Lemma bindReadReduce U m (p:Cursor 32) x q (f: DWORD -> Reader U):
  (readDWORD m p = readerOk x q) ->
  (bindRead readDWORD f m p) = f x m q.
Proof. move => H. rewrite /bindRead/bindRead_op/bind. simpl. simpl in H. by rewrite H. 
Qed. 

Lemma applyRoundtripTarget {Y} {m:Mem} {q:DWORD} {d x w} {f: DWORD -> Reader Y} : 
  (f d m q = readerOk x w) -> 
  (forall p, memIs m p q (encodeRel d p) -> bind readJumpTarget f m p = readerOk x w).
Proof. 
  move => H pos.  
  rewrite /readJumpTarget.
  move => MI. 
  rewrite /encodeRel in MI.
  case E: pos => [p |]. rewrite E in MI. 
  have RT := roundtrip MI. rewrite assoc. 
  simpl (getReader _) in RT. 
  rewrite (bindReadReduce _ RT).
  rewrite assoc. 
  rewrite bindGetCursor. rewrite id_l.  
  have RDN := readDWORD_next RT.  rewrite RDN.
  have MATHS: addB (p +# 4) (subB d (p +# 4)) = d. 
    apply toZp_inj. 
    Require Import bitsopsprops. Require Import zmodp ssralg.
    Import GRing.Theory.
    rewrite toZp_addB toZp_subB toZp_addB toZp_fromNat.
    set X := (toZp p + 4%:R)%R. 
    by rewrite addrCA addrN addr0. 
  rewrite MATHS.     congruence.

  by rewrite E in MI. 
Qed. 

Lemma roundtripInstr m (p p':DWORD) instr : 
  memIs m p p' (encodeInstr p instr) -> readInstr m p = readerOk instr p'.
Proof. 
simpl getReader. destruct instr; rewrite /encode /encodeInstr /read /readInstr.

(* UOP *)
rewrite /encodeUOP /encodeUnaryOp.
destruct dword; destruct op; 
  (apply: applyRoundtripCat => q; unfoldDM; apply: (applyRoundtrip (X:=BITS3RegMem_readerType)); by simpEq).

(* BOP *) 
rewrite /encodeBOP/encodeOpcode.
destruct ds;    apply (applyRoundtripCat (X:=BYTE_readerType)) => ?. 

(* ds = DstSrcRR dst src *)
   destruct op; destruct dword; (unfoldDM; rewrite /decodeOtherInstr /split2; simpEq;
      apply: (applyRoundtrip (X:=BITS3RegMem_readerType)); by rewrite !encRegK). 
(* ds = DstSrcRM dst src *)
    destruct op; destruct dword; (unfoldDM; rewrite /decodeOtherInstr /split2; simpEq;
      apply: (applyRoundtrip (X:=BITS3RegMem_readerType)); by rewrite !encRegK). 
(* ds = DstSrcMR dst src *)
    destruct op; destruct dword; (unfoldDM; rewrite /decodeOtherInstr /split2; simpEq;
      apply: (applyRoundtrip (X:=BITS3RegMem_readerType)); by rewrite !encRegK). 
(* ds = DstSrcRI dst src *)
    destruct dword.
    (unfoldDM; rewrite /decodeOtherInstr; simpEq; rewrite /split2; simpEq). 
    apply: (applyRoundtripCat (X:=BITS3RegMem_readerType)) => ?. apply: applyRoundtrip. 
    by rewrite !encBinOpK. 
    (unfoldDM; rewrite /decodeOtherInstr; simpEq; rewrite /split2; simpEq). 
    apply: (applyRoundtripCat (X:=BITS3RegMem_readerType)) => ?. apply: applyRoundtrip. 
    by rewrite !encBinOpK. 
(* ds = DstSrcMI dst src *)
    destruct dword;
    (unfoldDM; rewrite /decodeOtherInstr; simpEq; rewrite /split2; simpEq;
    do !(apply: (applyRoundtripCat (X:=BITS3RegMem_readerType)) => ?);
    apply applyRoundtrip; by rewrite !encBinOpK).

(* BITOP *)
destruct bit;
  (apply applyRoundtripCat => ?;
  unfoldDM; 
  rewrite /split2; simpEq; rewrite /split2;
  apply: (applyRoundtripCat (X:=BYTE_readerType)) => ?; simpEq).

 - apply: (applyRoundtripCat (X:=BITS3RegMem_readerType)) => ?. 
   rewrite high_catB low_catB; simpEq;
    apply applyRoundtrip; by rewrite !encBitOpK. 
  - simpEq; rewrite /split2; simpEq. rewrite high_catB. simpEq.  
    apply: (applyRoundtrip (X:=BITS3RegMem_readerType)); rewrite low_catB high_catB; 
    by rewrite !encRegK encBitOpK. 

(* TESTOP *)
  destruct src. 
  destruct dword; apply applyRoundtripCat => ?;
  rewrite /split2; simpEq; unfoldDM;
  apply: (applyRoundtripCat (X:=BITS3RegMem_readerType)) => ?; simpEq;
  by apply applyRoundtrip.

  destruct dword; apply applyRoundtripCat => ?;
  rewrite /split2; simpEq; unfoldDM;
  apply: (applyRoundtrip (X:=BITS3RegMem_readerType)); by rewrite encRegK.

(* MOVOP *)
  destruct ds. 
  (* ds = DstSrcRR dst src *)
  destruct dword;
    (rewrite /encodeBOP; apply applyRoundtripCat => ?;
    rewrite /split2; simpEq; unfoldDM;
    apply: (applyRoundtrip (X:=BITS3RegMem_readerType)); by rewrite encRegK). 

(* ds = DstSrcRM dst src *)
  destruct dword;
    (rewrite /encodeBOP; do !(apply applyRoundtripCat => ?);
    rewrite /split2; simpEq; unfoldDM;
    apply: (applyRoundtrip (X:=BITS3RegMem_readerType)); by rewrite encRegK). 

(* ds = DstSrcMR dst src *)
  destruct dword;
    (rewrite /encodeBOP; do !(apply applyRoundtripCat => ?);
    rewrite /split2; simpEq; unfoldDM;
    apply: (applyRoundtrip (X:=BITS3RegMem_readerType)); by rewrite encRegK). 

(* ds = DstSrcRI dst src *)
    destruct dword. 
    (* dword = true *)
    rewrite /encodeBOP. apply applyRoundtripCat => ?.
    case: dst. case; unfoldDM; rewrite /decodeOtherInstr; rewrite split2app; simpEq;
    apply applyRoundtrip; by rewrite encRegK. 
    unfoldDM; rewrite /decodeOtherInstr; rewrite split2app; simpEq;
    apply applyRoundtrip; by rewrite encRegK. 
    (* dword = false *)
    rewrite /encodeBOP. apply applyRoundtripCat => ?. 
    unfoldDM; rewrite /split2; simpEq. 
    apply: (applyRoundtripCat (X:=BITS3RegMem_readerType)) => ?.
    by apply applyRoundtrip. 
(* ds = DstSrcMI dst src *)
    destruct dword;
    (rewrite /encodeBOP;
    apply applyRoundtripCat => ?;
    unfoldDM; rewrite /split2; simpEq;
    apply: (applyRoundtripCat (X:=BITS3RegMem_readerType)) => ?;
    by apply applyRoundtrip).

(* SHIFT OP *)
destruct count. 
(* ShiftCountCL *)
destruct dword;
(apply applyRoundtripCat => ?;
rewrite /split2; simpEq; unfoldDM;
apply: (applyRoundtrip (X:=BITS3RegMem_readerType));
by rewrite encShiftOpK).
(* ShiftCountI c *)
destruct dword.
case EQ: (c == #1). 
rewrite (eqP EQ); apply applyRoundtripCat => ?;
rewrite /split2; simpEq; unfoldDM;
apply: (applyRoundtrip (X:=BITS3RegMem_readerType));
by rewrite encShiftOpK. 

apply applyRoundtripCat => ?.  
rewrite /split2; simpEq; unfoldDM.
apply: (applyRoundtripCat (X:=BITS3RegMem_readerType)) => ?.  
apply applyRoundtrip;
by rewrite encShiftOpK. 

case EQ: (c == #1). 
rewrite (eqP EQ); 
apply (applyRoundtripCat) => ?. 
rewrite /split2; simpEq; unfoldDM.
apply: (applyRoundtrip (X:=BITS3RegMem_readerType));
by rewrite encShiftOpK. 
 
apply applyRoundtripCat => ?.
rewrite /split2; simpEq; unfoldDM;
apply: (applyRoundtripCat (X:=BITS3RegMem_readerType)) => ?.
apply: (applyRoundtrip);
by rewrite encShiftOpK. 

(* MUL *)
apply applyRoundtripCat => ?.
unfoldDM; rewrite /split2; simpEq.
by apply (applyRoundtrip (X:=BITS3RegMem_readerType)).

(* IMUL *)
apply applyRoundtripCat => ?.
unfoldDM; rewrite /split2; simpEq.
apply: applyRoundtripCat => ?.
rewrite eq_refl. 
apply (applyRoundtrip (X:=BITS3RegMem_readerType)).
by rewrite encRegK. 

(* LEA *)
apply applyRoundtripCat => ?.
unfoldDM; rewrite /split2; simpEq. 
apply (applyRoundtrip (X:=BITS3RegMem_readerType)).
by rewrite encRegK.

(* JCC *)
apply: applyRoundtripCons.  
apply: applyRoundtripCons.  
move => MI.
(*rewrite /split2app.*)
have:  #b "1000" ## encCondition cc ## ~~ cv == #x"AF"  = false.  
by destruct cc; destruct cv. 
move => H. rewrite H. 
rewrite /split2. set S := (_ == _). 
have: S = false. by destruct cc; destruct cv. move => H'. 
rewrite H'. 
rewrite split3app. simpEq. 
rewrite encConditionK. 
apply: applyRoundtripTarget => //. 
destruct cv; by rewrite /retn/=/unitRead_op. 
done. 

(* PUSH *)
destruct src.
  (* SrcI *)
  apply applyRoundtripCat => ?. 

  unfoldDM; rewrite /split2; simpEq;
  by apply applyRoundtrip.  

  (* SrcM *)
  apply applyRoundtripCat => ?. 
  unfoldDM; rewrite /split2. simpEq; 
  by apply (applyRoundtrip (X:=BITS3RegMem_readerType)).  

  (* SrcR *)
  apply applyRoundtrip. 
  case r; [by case | done]. 

(* POP *)
apply applyRoundtripCat => ?.
unfoldDM; rewrite /split2; simpEq.
apply (applyRoundtrip (X:=BITS3RegMem_readerType)).
by simpEq. 

(* CALL *)
destruct src. 
  (* SrcI *)
  apply: applyRoundtripCons.
  unfoldDM.
  apply: applyRoundtripTarget => //. 

  (* SrcM *)
  apply applyRoundtripCat => ?. 
  unfoldDM; rewrite /split2. 
  simpEq. 
  apply (applyRoundtrip (X:=BITS3RegMem_readerType)). by simpEq. 

  (* SrcR *)  
  (* Missing decoding!! *) 
  apply applyRoundtripCat => ?. 
  unfoldDM; rewrite /split2. 
  apply (applyRoundtrip (X:=BITS3RegMem_readerType)). by simpEq. 


(* JMP *)
destruct src. 
  
  (* SrcI *)
  apply applyRoundtripCons.  
  unfoldDM. 
  apply: applyRoundtripTarget => //. 
  
  (* SrcM *)
  apply applyRoundtripCat => ?. 
  unfoldDM; rewrite /split2. 
  simpEq. 
  apply (applyRoundtrip (X:=BITS3RegMem_readerType)). by simpEq. 
  
  (* SrcR *)
  apply applyRoundtripCat => ?. 
  unfoldDM; rewrite /split2.
  apply (applyRoundtrip (X:=BITS3RegMem_readerType)). by simpEq. 

(* CLC *)
by apply applyRoundtrip.  

(* STC *)
by apply applyRoundtrip.  

(* CMC *)
by apply applyRoundtrip.  

(* RET *)
case E: (size == zero _). 
apply  applyRoundtrip.  
unfoldDM; rewrite /split2. by rewrite (eqP E). 
apply: (applyRoundtripCat (X:=BYTE_readerType)) => ?. 
unfoldDM; rewrite /split2. 
by apply (applyRoundtrip (X:=WORD_readerType)).

(* HLT *)
by apply applyRoundtrip.  

(* OUT *)
destruct dword; 
  (apply applyRoundtripCat => ?;
  unfoldDM;
  by apply (applyRoundtrip (X:=BYTE_readerType))).

(* IN *)
destruct dword; 
  (apply applyRoundtripCat => ?;
  unfoldDM;
  by apply (applyRoundtrip (X:=BYTE_readerType))).

(* BADINSTR *)
by apply applyRoundtrip.  
Qed. 

