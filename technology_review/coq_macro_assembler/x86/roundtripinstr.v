Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq tuple fintype finfun.
Require Import bitsrep bitsprops bitsops reg instr mem encdechelp monad roundtrip 
               reader writer encinstr decinstr emb cursor.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Ltac simpEq :=
    repeat (match goal with |- context [?XX == ?YY] => 
      (try change (XX == YY) with false; try change (XX == YY) with true) end); cbv iota.
(*try replace (_ == _) with false by done;
        try replace (_ == _) with true by done).  *)

Lemma encodeNonSP : forall (r:NonSPReg), (encReg r == #b"100") = false.  
Proof. by case. Qed.


Instance RoundtripRegMem dword : Roundtrip (readRegMem dword) (@writeRegMem dword).
Proof.
move=> [regbits rm] p.
rewrite /readRegMem/writeRegMem.
case rm => [r | ms].
(* rm = DstR _ *)
apply: simrw_next' => {p}p _.
rewrite split3app encDWORDorBYTERegK. apply: simrw_retn.

(* rm = DstM m0 *)
  case: ms => [base indexAndScale offset] .
  case eq0: (offset == zero _). 

  (******* displacement 0 ********)
  (*-*) 
    rewrite (eqP eq0). 
    case: indexAndScale.

  (* Have index and scale *) 
    (***) move => [ix scale]. 
      apply: simrw_next' => {p}p _.
      rewrite split3app assoc.
      apply: simrw_next' => {p}p _.
      rewrite split3app encNonSPRegK encRegK encScaleK id_l fromNat0.
      apply: simrw_retn.

  (* Don't have index and scale *)
    (***) case: base => [n |].

      (* base is NonSP *)
      apply: simrw_next' => {p}p _.
      rewrite split3app. 
      rewrite /readSIB.
      rewrite (encodeNonSP n) encRegK. rewrite id_l fromNat0.
      apply: simrw_retn.

      (* base is SP *)
      apply: simrw_next' => {p}p _.
      rewrite split3app !eq_refl /readSIB !assoc. 
      apply: simrw_next' => {p}p _.
      rewrite fromNat0.
      apply: simrw_retn.

  (******* 8-bit or 32-bit displacement ********)
  (*-*) case E: (signTruncate _) => [b |]. 

(****** 8-bit displacement *********)
    case: indexAndScale.

    (* Have index and scale *)
    (***) move => [ix scale].
      apply: simrw_next' => {p}p _.
      rewrite split3app /readSIB !assoc.
      apply: simrw_next' => {p}p _.
      rewrite split3app encNonSPRegK encScaleK encRegK id_l. 
      apply: simrw_next' => {p}p _.
      rewrite (signTruncateK E).  
      apply: simrw_retn.

   (* Don't have index and scale *)
    (***) case: base => [n |]. 

      (* base is NonSP *)
      apply: simrw_next' => {p}p _.
      rewrite split3app /readSIB eq_refl encodeNonSP id_l encRegK. 
      apply: simrw_next' => {p}p _.
      rewrite (signTruncateK E). 
      apply: simrw_retn. 

      (* base is SP *)
      apply: simrw_next' => {p}p _.
      rewrite split3app /readSIB !assoc. 
      apply: simrw_next' => {p}p _.
      rewrite split3app id_l.  
      apply: simrw_next' => {p}p _.
      rewrite (signTruncateK E).  
      apply: simrw_retn. 

(******* 32-bit displacement ********)
(*-*) case: indexAndScale.  

  (* Have index and scale *)
  (*+*) move => [ix scale]. 
    apply: simrw_next' => {p}p _.
    rewrite split3app/readSIB.
    Ltac decide_ifs := repeat (match goal with
      | |- context [ if ?b then _ else _ ] => change b with true
      | |- context [ if ?b then _ else _ ] => change b with false
      end; cbv iota).
    decide_ifs. rewrite assoc.
    apply: simrw_next' => {p}p _.
    rewrite split3app encNonSPRegK encScaleK encRegK id_l. 
    apply: simrw_bind => {p}p.
    apply: simrw_retn. 

   (* Don't have index and scale *)
    (***) case: base => [n |]. 

      (* base is NonSP *)
    apply: simrw_next' => {p}p _.
    rewrite split3app /readSIB encodeNonSP id_l encRegK. 
    decide_ifs. rewrite !id_l.
    apply: simrw_bind => {p}p.
    apply: simrw_retn. 

      (* base is SP *)
    apply: simrw_next' => {p}p _.
    rewrite split3app /readSIB.
    decide_ifs. rewrite assoc.
    apply: simrw_next' => {p}p _.
    rewrite split3app id_l.  
    apply: simrw_bind => {p}p.
    apply: simrw_retn. 
Qed.

Instance RoundtripTarget : Roundtrip readJumpTarget encodeJumpTarget.
Proof. 
move => d p. 
rewrite /readJumpTarget/encodeJumpTarget. 
constructor.
constructor.
destruct d. 
destruct p; last exact: simrw_fail.
apply: simrw_bind_end => p'.
have ->: addB (b +# 4) (subB d (b +# 4)) = d. 
  apply toZp_inj. 
  Require Import bitsopsprops zmodp ssralg.
  Import GRing.Theory.
  rewrite toZp_addB toZp_subB toZp_addB toZp_fromNat.
  set X := (toZp b + 4%:R)%R. 
  by rewrite addrCA addrN addr0. 
apply: simrw_retn.
Qed. 

Ltac unfoldDM := (let DM := fresh in set DM:= decMap _; hnf in DM; rewrite /DM {DM}).

(*=RoundtripInstr *)
Instance RoundtripInstr : Roundtrip readInstr encodeInstr.
(*=End *)
Proof. 
move=> d p. rewrite /readInstr/encodeInstr.
elim d. 

(* UOP *)
rewrite /encodeUOP /encodeUnaryOp.
elim; elim; move => dst;
    apply: simrw_bind => {p}p; unfoldDM; rewrite <-doRet;
    apply: simrw_bind => {p}p;
    apply: simrw_retn.

(* BOP *) 
rewrite /encodeBOP/encodeOpcode => dword op dst.
destruct dst; apply: simrw_bind => {p}p.
(* ds = DstSrcRR dst src *) 
   destruct op; destruct dword;
   apply: simrw_bind_end => {p}p; rewrite !encDWORDorBYTERegK; apply: simrw_retn. 
(* ds = DstSrcRM dst src *)
    destruct op; destruct dword; 
    apply: simrw_bind_end => {p}p; rewrite !encDWORDorBYTERegK; apply: simrw_retn. 
(* ds = DstSrcMR dst src *)
    destruct op; destruct dword; 
    apply: simrw_bind_end => {p}p; rewrite !encDWORDorBYTERegK; apply: simrw_retn. 
(* ds = DstSrcRI dst src *)
    destruct op; destruct dword; apply: simrw_bind => {p}p; 
    apply: simrw_bind_end => {p}p; 
    rewrite !encBinOpK; apply: simrw_retn. 
(* ds = DstSrcMI dst src *)
    destruct dword;    
    apply: simrw_bind => {p}p; apply: simrw_bind_end => {p}p;
    rewrite !encBinOpK; apply: simrw_retn.  

(* BITOP *)
destruct bit;
  (apply: simrw_bind => {p}p;
  rewrite /split2; simpEq; rewrite /split2;
  apply: simrw_bind => {p}p; simpEq).

 (*-*) apply: simrw_bind => {p}p. 
   rewrite /split2; simpEq; rewrite /split2;
   rewrite high_catB low_catB; simpEq;
    apply: simrw_bind_end => {p}p; rewrite !encBitOpK; apply: simrw_retn. 
 (*- *) simpEq; rewrite /split2; simpEq. rewrite high_catB. simpEq.  
    apply: simrw_bind_end => {p}p ; rewrite low_catB high_catB; 
    rewrite !encDWORDorBYTERegK encBitOpK; apply: simrw_retn. 

(* TESTOP *)
  destruct src. 
  destruct d0; apply: simrw_bind => {p}p;
  apply: simrw_bind => {p}p; simpEq;
  apply: simrw_bind_end => {p}p; apply: simrw_retn.

  destruct d0; apply: simrw_bind => {p}p; 
  apply: simrw_bind_end => {p}p; rewrite encDWORDorBYTERegK; apply: simrw_retn.

(* MOVOP *)
  destruct ds. 
  (* ds = DstSrcRR dst src *)
  destruct d0;
    (rewrite /encodeBOP; apply: simrw_bind => {p}p;
    apply: simrw_bind_end => {p}p; rewrite encDWORDorBYTERegK; apply: simrw_retn). 

(* ds = DstSrcRM dst src *)
  destruct d0;
    (rewrite /encodeBOP; apply: simrw_bind => {p}p;
    apply: simrw_bind_end => {p}p; rewrite encDWORDorBYTERegK; apply: simrw_retn). 

(* ds = DstSrcMR dst src *)
  destruct d0;
    (rewrite /encodeBOP; apply: simrw_bind => {p}p;
    apply: simrw_bind_end => {p}p; rewrite encDWORDorBYTERegK; apply: simrw_retn). 

(* ds = DstSrcRI dst src *)
    destruct d0.
    rewrite /encodeBOP; apply: simrw_bind => {p}p. 
    destruct dst.
    destruct n;
    apply: simrw_bind_end => {p}p; apply: simrw_retn.  
    apply: simrw_bind_end => {p}p; apply: simrw_retn. 

    destruct dst; apply: simrw_bind => {p}p;
    apply: simrw_bind => {p}p; apply: simrw_bind_end => {p}p; apply: simrw_retn. 
(* ds = DstSrcMI dst src *)
    destruct d0;
    (rewrite /encodeBOP;
    apply: simrw_bind => {p}p;
    apply: simrw_bind => {p}p;
    apply: simrw_bind_end => {p}p; apply: simrw_retn).

(* MOVX *)
  destruct signextend; destruct w => dst src;
  apply: simrw_bind => {p}p;
  apply: simrw_bind => {p}p; 
  apply: simrw_bind_end => {p}p; 
  rewrite encRegK;  
  apply: simrw_retn. 

(* SHIFT OP *)
destruct count. 
(* ShiftCountCL *)
destruct d0;
(apply: simrw_bind => {p}p;
apply: simrw_bind_end => {p}p;
rewrite encShiftOpK; apply: simrw_retn).
(* ShiftCountI c *)
destruct d0.
case EQ: (c == #1). 
rewrite (eqP EQ); apply: simrw_bind => {p}p;
apply: simrw_bind_end => {p}p;
rewrite encShiftOpK; apply: simrw_retn. 

apply: simrw_bind => {p}p;
apply: simrw_bind => {p}p.
apply: simrw_bind_end => {p}p;
rewrite encShiftOpK; apply: simrw_retn.

case EQ: (c == #1). 
rewrite (eqP EQ); 
apply: simrw_bind => {p}p.
apply: simrw_bind_end => {p}p;
rewrite encShiftOpK; apply: simrw_retn. 
 
apply: simrw_bind => {p}p.
apply: simrw_bind => {p}p.
apply: simrw_bind_end => {p}p.
rewrite encShiftOpK. 
apply: simrw_retn.

(* MUL *)
destruct d0 => src; apply: simrw_bind => {p}p;
apply: simrw_bind_end => {p}p;
apply: simrw_retn.

(* IMUL *)
move => dst src. 
apply: simrw_bind => {p}p.
apply: simrw_bind => {p}p.
rewrite eq_refl. 
apply: simrw_bind_end => {p}p.
rewrite encRegK. 
apply: simrw_retn.  

(* LEA *)
move => dst src. 
apply: simrw_bind => {p}p.
apply: simrw_bind_end => {p}p.
rewrite encRegK.
apply: simrw_retn.

(* JCC *)
move => cc cv tgt. 
apply: simrw_bind => {p}p. 
apply: simrw_bind => {p}p. 
(*rewrite /split2app.*)
have:  #b "1000" ## encCondition cc ## ~~ cv == #x"AF"  = false by destruct cc; destruct cv. 
move ->. 
have:  #b "1000" ## encCondition cc ## ~~ cv == #x"B6"  = false by destruct cc; destruct cv. 
move ->. 
have:  #b "1000" ## encCondition cc ## ~~ cv == #x"B7"  = false by destruct cc; destruct cv. 
move ->. 
have:  #b "1000" ## encCondition cc ## ~~ cv == #x"BE"  = false by destruct cc; destruct cv. 
move ->. 
have:  #b "1000" ## encCondition cc ## ~~ cv == #x"BF"  = false by destruct cc; destruct cv. 
move ->. 
rewrite /split2. set S := (_ == _). 
have: S = false. by destruct cc; destruct cv. move => H'. 
rewrite H'. 
rewrite split3app. simpEq. 
rewrite encConditionK. 
apply: simrw_bind_end => {p}p. 
destruct cv; apply: simrw_retn. 

(* PUSH *)
destruct src.
  (* SrcI *)
  case E: (signTruncate _) => [b |].   

    apply: simrw_bind => {p}p. 
    apply: simrw_bind_end => {p}p.
    rewrite (signTruncateK E).  
    apply: simrw_retn.

    apply: simrw_bind => {p}p. 
    apply: simrw_bind_end => {p}p.
    apply: simrw_retn. 

  (* SrcM *)
  apply: simrw_bind => {p}p.
  apply: simrw_bind_end => {p}p.
  apply: simrw_retn.

  (* SrcR *)
  apply: simrw_bind_end => {p}p.
  case r; [case|]; apply: simrw_retn. 

(* POP *)
elim => [r | m]. 
apply: simrw_bind_end => {p}p.  
have:  decMap (#b "01011" ## r)= None.
destruct r. by destruct n. done. 
move ->.
destruct r. destruct n; apply: simrw_retn. 
apply: simrw_retn. 

apply: simrw_bind => {p}p.  
apply: simrw_bind_end => {p}p.  
apply: simrw_retn. 

(* CALL *)
elim => [t | m | r].
  (* JmpTgtI *)
  apply: simrw_bind => {p}p.
  apply: simrw_bind_end => {p}p. 
  apply: simrw_retn. 

  (* SrcM *)
  apply: simrw_bind => {p}p.
  apply: simrw_bind_end => {p}p.  
  apply: simrw_retn. 

  (* SrcR *)  
  apply: simrw_bind => {p}p.
  apply: simrw_bind_end => {p}p.  
  apply: simrw_retn.

(* JMP *)
elim => [t | m | r]. 
  
  (* SrcI *)
  apply: simrw_bind => {p}p.
  apply: simrw_bind_end => {p}p.  
  apply: simrw_retn. 
  
  (* SrcM *)
  apply: simrw_bind => {p}p.
  apply: simrw_bind_end => {p}p.  
  apply: simrw_retn. 
  
  (* SrcR *)
  apply: simrw_bind => {p}p.
  apply: simrw_bind_end => {p}p.  
  apply: simrw_retn. 

(* CLC *)
apply: simrw_bind_end => {p}p. 
apply: simrw_retn.

(* STC *)
apply: simrw_bind_end => {p}p. 
apply: simrw_retn.

(* CMC *)
apply: simrw_bind_end => {p}p. 
apply: simrw_retn.

(* RET *)
move => size. case E: (size == zero _). 
apply: simrw_bind_end => {p}p.  
rewrite (eqP E). 
apply: simrw_retn. 

apply: simrw_bind => {p}p. 
apply: simrw_bind_end => {p}p. 
apply: simrw_retn. 

(* OUT *)
move => dword port. 
destruct dword; 
  (apply: simrw_bind => {p}p;
  apply: simrw_bind_end => {p}p; apply: simrw_retn).

(* IN *)
move => dword port.
destruct dword; 
  (apply: simrw_bind => {p}p;
  apply: simrw_bind_end => {p}p; apply: simrw_retn).

(* HLT *)
apply: simrw_bind_end => {p}p. 
apply: simrw_retn.

(* BADINSTR *)
constructor.
Qed. 