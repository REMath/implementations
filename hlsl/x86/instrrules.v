(*===========================================================================
    Rules for x86 instructions in terms of [safe]
  ===========================================================================*)
Require Import ssreflect ssrbool ssrnat eqtype seq fintype tuple.
Require Import procstate procstatemonad bitsops bitsprops bitsopsprops.
Require Import SPred septac spec safe triple basic.
Require Import instr decinstr eval monad monadinst reader pointsto cursor.
Require Import Setoid RelationClasses Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Relations.
Require Import instrsyntax. 

Local Open Scope instr_scope.

(* TODO: needed now? *)
Lemma TRIPLE_nopost P (c: ST unit):
  TRIPLE (P ** ltrue) c ltrue ->
  forall s: ProcState, (P ** ltrue) (toPState s) ->
    exists s', c s = Success _ (s', tt).
Proof.
  move=> HTRIPLE s Hs. move/(_ s Hs): HTRIPLE => [s' [Hs' _]]. eauto.
Qed.

Section UnfoldSpec.
  Transparent ILPre_Ops.

  Lemma TRIPLE_safe_gen instr P Q (i j: DWORD) sij:
    eq sij |-- i -- j :-> instr ->
    (forall (R: SPred),
     TRIPLE (EIP ~= j ** P ** eq sij ** R) (evalInstr instr)
            (Q ** R)) ->
    |> safe @ Q |-- safe @ (EIP ~= i ** P ** eq sij).
  Proof.
    move => Hsij HTRIPLE k R /= HQ. rewrite /spec_fun /= in HQ. move=> s Hs.
    destruct k. (* everything's safe in 0 steps *)
    - exists s. reflexivity.
    rewrite /doMany -/doMany assoc.
    (* TODO: This is clumsy. Make it more like in attic/instrrules.v. *)
    move: s Hs. apply: TRIPLE_nopost.
    eapply triple_letGetReg. 
    - by ssimpl.
    rewrite assoc.
    eapply triple_letReadSep.
    - rewrite ->Hsij. by ssimpl.
    rewrite assoc. eapply triple_seq.
    - eapply triple_setRegSepGen. by ssimpl.
    eapply triple_seq.
    - triple_apply HTRIPLE.
    move=> s Hs.
    edestruct (HQ k) as [f Hf]; first omega.
    - rewrite ->lentails_eq. rewrite ->sepSPA, <-lentails_eq.
      eassumption.
    exists f. by split.
  Qed.
End UnfoldSpec.

Lemma TRIPLE_safe instr P Q (i j: DWORD):
  (forall (R: SPred),
   TRIPLE (EIP ~= j ** P ** R) (evalInstr instr) (Q ** R)) ->
  |-- (|> safe @ Q -->> safe @ (EIP ~= i ** P)) <@ (i -- j :-> instr).
Proof.
  move=> H. rewrite /spec_reads. specintros => s Hs. autorewrite with push_at.
  rewrite sepSPA. apply limplValid.
  eapply TRIPLE_safe_gen; [eassumption|]. move=> R. triple_apply H.
Qed.

Lemma TRIPLE_basic instr P Q:
  (forall (R: SPred), TRIPLE (P ** R) (evalInstr instr) (Q ** R)) ->
  |-- basic P instr Q.
Proof.
  move=> H. rewrite /basic. specintros => i j.
  rewrite ->(@spec_later_weaken (safe @ (EIP~=j ** Q))).
  apply TRIPLE_safe => R. triple_apply H.
Qed.

(* A broader simpl sends Coq into a loop sometimes. *)
Ltac command_simpl := rewrite [X in TRIPLE _ X _]/=.

(*---------------------------------------------------------------------------
    Helpers for pieces of evaluation (adapted from spechelpers and
    triplehelpers)
  ---------------------------------------------------------------------------*)

Definition OSZCP o s z c p := 
  (flagIs OF o ** flagIs SF s ** flagIs ZF z ** flagIs CF c ** flagIs PF p).

Definition OSZCP_Any :=
  (flagAny OF ** flagAny SF ** flagAny ZF ** flagAny CF ** flagAny PF).

Lemma evalReg_rule r v c Q : 
  forall S,
  TRIPLE (r~=v ** S) (c v) Q -> 
  TRIPLE (r~=v ** S) (bind (evalReg true r) c) Q.
Proof. by apply triple_letGetRegSep. Qed. 

Lemma getReg_rule r v c Q : 
  forall S,
  TRIPLE (r~=v ** S) (c v) Q -> 
  TRIPLE (r~=v ** S) (bind (getRegFromProcState r) c) Q.
Proof. by apply triple_letGetRegSep. Qed. 

Lemma evalMemSpec_rule (r:Reg) p offset c Q :
  forall S,
  TRIPLE (r ~= p ** S) (c (addB p offset)) Q ->
  TRIPLE (r ~= p ** S) (bind (evalMemSpec (mkMemSpec r None offset)) c) Q.
Proof. rewrite /evalMemSpec assoc => S T. apply triple_letGetRegSep. by rewrite id_l. Qed. 

Lemma triple_pre_introFlags P comp Q :
  (forall o s z c p, TRIPLE (OSZCP o s z c p ** P) comp Q) ->
  TRIPLE (OSZCP_Any ** P) comp Q.
Proof. 
  rewrite /OSZCP_Any /OSZCP /flagAny.
  (* TODO: could use an sdestruct tactic for TRIPLE. *)
  move=> H s Hs.
  sdestruct: Hs => fo Hs.
  sdestruct: Hs => fs Hs.
  sdestruct: Hs => fz Hs.
  sdestruct: Hs => fc Hs.
  sdestruct: Hs => fp Hs.
  eapply H. eassumption.
Qed.

(*---------------------------------------------------------------------------
    First, rules for MOV
  ---------------------------------------------------------------------------*)

(* Register to register *)
Lemma MOV_RR_rule (r1 r2:Reg) v:
  |-- basic (r1? ** r2 ~= v) (mov r1, r2) (r1 ~= v ** r2 ~= v).
Proof.
  rewrite /regAny. specintro => v0.
  apply TRIPLE_basic => R.
  rewrite /evalInstr/evalMOV/RegMemPairToDstSrc. 
  triple_apply triple_letGetRegSep.
  command_simpl.
  triple_apply triple_setRegSep.
Qed. 

(* Immediate to register *)
Lemma MOV_RI_rule (r:Reg) (v:DWORD) :
  |-- basic (r?) (mov r, v) (r ~= v).
Proof.
  rewrite /regAny. specintro => v0.
  apply TRIPLE_basic => R.
  rewrite /evalInstr/evalMOV/RegMemPairToDstSrc.
  command_simpl.
  triple_apply triple_setRegSep.
Qed.

(* Register to memory *)
Lemma MOV_MR_rule (p: DWORD) (r1 r2: Reg) offset (v1 v2:DWORD) :
  |-- basic (r1~=p ** p +# offset :-> v1 ** r2~=v2)
            (mov [r1 + offset], r2)
            (r1~=p ** p +# offset :-> v2 ** r2~=v2).
Proof.
  apply TRIPLE_basic => R.
  rewrite /evalInstr/evalMOV /RegMemPairToDstSrc.
  triple_apply triple_letGetRegSep.
  triple_apply evalMemSpec_rule.
  triple_apply triple_setDWORDSep.
Qed.

Lemma MOV_MbR_rule (p: DWORD) (r1 r2:Reg) offset (v1:BYTE) (v2:DWORD) :
  |-- basic (r1 ~= p ** p +# offset :-> v1 ** r2 ~= v2)
            (mov byte [r1 + offset], r2)
            (r1 ~= p ** p +# offset :-> (low 8 v2:BYTE) ** r2 ~= v2).
Proof.
  apply TRIPLE_basic => R.
  rewrite /evalInstr/evalMOV /RegMemPairToDstSrc.
  rewrite /evalReg assoc. 
  triple_apply triple_letGetRegSep.
  rewrite id_l. 
  triple_apply evalMemSpec_rule.
  triple_apply triple_setBYTESep.
Qed.


Lemma MOV_MbI_rule (pd:BITS 32) (r1:Reg) offset (v1:BYTE) (v2:DWORD) :
  |-- basic (r1 ~= pd ** pd +# offset :-> v1)
            (mov byte [r1 + offset], (SrcI v2))
            (r1 ~= pd ** pd +# offset :-> (low 8 v2:BYTE)).
Proof.
  apply TRIPLE_basic => R.
  rewrite /evalInstr/evalMOV /RegMemPairToDstSrc.
  triple_apply evalMemSpec_rule.   
  triple_apply triple_setBYTESep.
Qed.


(* Immediate to memory *)
Lemma MOV_MI_rule dword (pd:BITS 32) (r:Reg) offset (v w:DWORDorBYTE dword) :
  |-- basic (r ~= pd ** pd +# offset :-> v)
            (MOVOP _ (DstSrcMI dword (mkMemSpec r None #offset) w))
            (r ~= pd ** pd +# offset :-> w).
Proof.
  apply TRIPLE_basic => R.
  rewrite /evalInstr/evalMOV.
  triple_apply evalMemSpec_rule. 
  triple_apply (@triple_setDWORDorBYTESep dword).
Qed.

(* Memory to register *)
Lemma MOV_RM_rule (pd:BITS 32) (r1 r2:Reg) offset (v:DWORDorBYTE true) :
  |-- basic (r1? ** r2 ~= pd ** pd +# offset :-> v)
            (mov r1, [r2 + offset])
            (r1 ~= v ** r2 ~= pd ** pd +# offset :-> v).
Proof.
  rewrite /regAny. specintro => v0.
  apply TRIPLE_basic => R.
  rewrite /evalInstr/evalMOV /RegMemPairToDstSrc.
  triple_apply evalMemSpec_rule. 
  triple_apply triple_letGetDWORDSep.
  triple_apply triple_setRegSep. 
Qed. 

Lemma MOV_RM0_rule (pd:BITS 32) (r1 r2:Reg) (v:DWORDorBYTE true) :
  |-- basic (r1? ** r2 ~= pd ** pd :-> v)
            (mov r1, [r2])
            (r1 ~= v ** r2 ~= pd ** pd :-> v).
Proof.
  have RULE := @MOV_RM_rule pd r1 r2 0 v. 
  by rewrite addB0 in RULE.
Qed. 

Lemma MOV_M0R_rule (pd:BITS 32) (r1 r2:Reg) (v1 v2:DWORDorBYTE true) :
  |-- basic (r1 ~= pd ** pd :-> v1 ** r2 ~= v2)
            (mov [r1], r2)
            (r1 ~= pd ** pd :-> v2 ** r2 ~= v2).
Proof.
  have RULE := @MOV_MR_rule pd r1 r2 0 v1 v2.
  by rewrite addB0 in RULE.
Qed. 


(*---------------------------------------------------------------------------
    Unary operations
  ---------------------------------------------------------------------------*)

Lemma triple_doUpdateZPS S Q n (v: BITS n) c z p s:
  TRIPLE (flagIs ZF (v == #0) **
          flagIs PF (lsb v) **
          flagIs SF (msb v) ** S) c Q ->
  TRIPLE (flagIs ZF z ** flagIs PF p ** flagIs SF s ** S) (do!updateZPS v; c) Q.
Proof.
  move=> H. rewrite assoc /updateZPS assoc. 
  triple_apply triple_doSetFlagSep.
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doSetFlagSep.
  triple_apply H.
Qed.

(* Special case for increment *)
Lemma INC_R_rule (r:Reg) (v:DWORD) o s z c pf:
  let w := incB v in
  |-- basic (r~=v ** OSZCP o s z c pf) (inc r)
            (r~=w ** OSZCP (msb v!=msb w) (msb w) (w == #0) c (lsb w)).
Proof. 
  move => w. apply TRIPLE_basic => R.
  rewrite /evalInstr/evalDst/evalDstR.
  triple_apply evalReg_rule. rewrite /evalUnaryOp assoc /OSZCP.
  triple_apply triple_doSetFlagSep. rewrite assoc.
  triple_apply triple_doUpdateZPS. rewrite id_l.
  triple_apply triple_setRegSep.
Qed. 

(* Special case for decrement *)
Lemma DEC_R_rule (r:Reg) (v:DWORD) o s z c pf :
  let w := decB v in
  |-- basic (r~=v ** OSZCP o s z c pf) (dec r)
            (r~=w ** OSZCP (msb v!=msb w) (msb w) (w == #0) c (lsb w)).
Proof. 
  (* Copy-paste of the INC_R_rule proof *)
  move => w. apply TRIPLE_basic => R.
  rewrite /evalInstr/evalDst/evalDstR.
  triple_apply evalReg_rule. rewrite /evalUnaryOp assoc /OSZCP.
  triple_apply triple_doSetFlagSep. rewrite assoc.
  triple_apply triple_doUpdateZPS. rewrite id_l.
  triple_apply triple_setRegSep.
Qed. 

(* Special case for not *)
Lemma NOT_R_rule (r:Reg) (v:DWORD):
  |-- basic (r~=v) (not r) (r~=invB v).
Proof. 
  apply TRIPLE_basic => R.
  rewrite /evalInstr/evalDst/evalDstR.
  triple_apply evalReg_rule.
  rewrite /evalUnaryOp id_l. 
  triple_apply triple_setRegSep. 
Qed. 

(* Special case for negation *)
Lemma NEG_R_rule (r:Reg) (v:DWORD) :
  let w := negB v in
  |-- basic
    (r~=v ** OSZCP_Any) (neg r)
    (r~=w ** OSZCP (msb v!=msb w) (msb w) (w == #0) (v != #0) (lsb w)).
Proof. 
  move => w. apply TRIPLE_basic => R.
  rewrite /evalInstr/evalDst/evalDstR.
  triple_apply evalReg_rule.
  rewrite /evalUnaryOp/evalArithUnaryOp.
  assert (HH := subB_equiv_addB_negB #0 v). rewrite /subB in HH. 
  assert (CARRY := sbb0B_carry v).
  case E: (sbbB false #0 v) => [carry res]. rewrite assoc.
  rewrite E in HH. rewrite E in CARRY. simpl snd in HH. simpl fst in CARRY.
  rewrite add0B in HH. rewrite HH. 
  rewrite CARRY.
  triple_apply triple_pre_introFlags => o s z c p. rewrite /OSZCP.
  triple_apply triple_doSetFlagSep. rewrite assoc.
  triple_apply triple_doSetFlagSep. rewrite assoc.
  triple_apply triple_doUpdateZPS. rewrite id_l. rewrite /w. 
  triple_apply triple_setRegSep.
Qed. 


(*---------------------------------------------------------------------------
    Binary operations
  ---------------------------------------------------------------------------*)

Lemma ADD_RI_rule (r1:Reg) v1 (v2:DWORD) carry v:
  splitmsb (adcB false v1 v2) = (carry,v) ->
  |-- basic (r1~=v1 ** OSZCP_Any) (add r1, v2)
            (r1~=v ** OSZCP (computeOverflow v1 v2 v) (msb v)
                            (v == #0) carry (lsb v)).
Proof.
  move => E. apply TRIPLE_basic => R.
  rewrite /evalInstr/evalDstSrc/evalDstR /RegMemPairToDstSrc.
  triple_apply evalReg_rule. 
  rewrite /evalBinOp/evalArithOpNoCarry E assoc. 
  triple_apply triple_pre_introFlags => o s z c p. rewrite /OSZCP.
  triple_apply triple_doSetFlagSep. rewrite assoc. 
  triple_apply triple_doSetFlagSep. rewrite assoc.
  triple_apply triple_doUpdateZPS. rewrite id_l. 
  triple_apply triple_setRegSep. 
Qed. 

Lemma ADD_RM_rule (pd:BITS 32) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat) carry v:
  splitmsb (adcB false v1 v2) = (carry,v) ->
  |-- basic (r1~=v1 ** r2 ~= pd ** pd +# offset :-> v2 ** OSZCP_Any)
            (add r1, [r2 + offset])
            (r1~=v ** r2 ~= pd ** pd +# offset :-> v2 **
             OSZCP (computeOverflow v1 v2 v) (msb v) (v == #0) carry (lsb v)).
Proof.
  move => E. apply TRIPLE_basic => R.
  rewrite /evalInstr/evalDstSrc/evalDstR /RegMemPairToDstSrc.
  triple_apply evalReg_rule. rewrite /evalBinOp/evalArithOpNoCarry assoc.
  triple_apply evalMemSpec_rule. rewrite assoc. 
  triple_apply triple_letGetDWORDSep. 
  triple_apply triple_pre_introFlags => o s z c p. rewrite /OSZCP.
  rewrite E assoc. 
  triple_apply triple_doSetFlagSep. rewrite assoc. 
  triple_apply triple_doSetFlagSep. rewrite assoc.
  triple_apply triple_doUpdateZPS. rewrite id_l. 
  triple_apply triple_setRegSep.
Qed. 

(*
Lemma ADD_RM_newrule (pd:BITS 32) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat) carry v:
  splitmsb (adcB false v1 v2) = (carry,v) ->
  |-- basic (r1~=v1 ** OSZCP_Any)
            (add r1, [r2 + offset])
            (r1~=v ** OSZCP (computeOverflow v1 v2 v) (msb v) (v == #0) carry (lsb v))
      <@ (r2 ~= pd ** pd +# offset :-> v2).
Proof.
  move => E. rewrite /basic. apply TRIPLE_safe_gen => R.
  rewrite /evalInstr/evalDstSrc/evalDstR /RegMemPairToDstSrc.
  triple_apply evalReg_rule. rewrite /evalBinOp/evalArithOpNoCarry assoc.
  triple_apply evalMemSpec_rule. rewrite assoc. 
  triple_apply triple_letGetDWORDSep. 
  triple_apply triple_pre_introFlags => o s z c p. rewrite /OSZCP.
  rewrite E assoc. 
  triple_apply triple_doSetFlagSep. rewrite assoc. 
  triple_apply triple_doSetFlagSep. rewrite assoc.
  triple_apply triple_doUpdateZPS. rewrite id_l. 
  triple_apply triple_setRegSep.
Qed. 
*)

Lemma SUB_RM_rule (pd:BITS 32) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat) carry v:
  sbbB false v1 v2 = (carry,v) ->
  |-- basic (r1~=v1 ** r2 ~= pd ** pd +# offset :-> v2 ** OSZCP_Any)
            (sub r1, [r2 + offset])
            (r1~=v ** r2 ~= pd ** pd +# offset :-> v2 **
             OSZCP (computeOverflow v1 v2 v) (msb v) (v == #0) carry (lsb v)).
Proof.
  move => E. apply TRIPLE_basic => R.
  rewrite /evalInstr/evalDstSrc/evalDstR /RegMemPairToDstSrc.
  triple_apply evalReg_rule. rewrite /evalBinOp/evalArithOpNoCarry assoc.
  triple_apply evalMemSpec_rule. rewrite assoc. 
  triple_apply triple_letGetDWORDSep. rewrite E assoc.
  triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
  triple_apply triple_doSetFlagSep. rewrite assoc. 
  triple_apply triple_doSetFlagSep. rewrite assoc.
  triple_apply triple_doUpdateZPS. rewrite id_l. 
  triple_apply triple_setRegSep. 
Qed.

Lemma ADC_RI_rule (r1:Reg) v1 (v2:DWORD) carry v o s z c p:
  splitmsb (adcB c v1 v2) = (carry,v) ->
  |-- basic (r1~=v1 ** OSZCP o s z c p) (adc r1, v2)
            (r1~=v ** OSZCP (computeOverflow v1 v2 v) (msb v)
                            (v == #0) carry (lsb v)).
Proof.
  move => E. apply TRIPLE_basic => R.
  rewrite /evalInstr/evalDstSrc/evalDstR /RegMemPairToDstSrc.
  triple_apply evalReg_rule. 
  rewrite /evalBinOp/evalArithOp assoc.
  rewrite /OSZCP.
  triple_apply triple_letGetFlag.
  - by ssimpl.
  rewrite E assoc.
  triple_apply triple_doSetFlagSep. rewrite assoc. 
  triple_apply triple_doSetFlagSep. rewrite assoc.
  triple_apply triple_doUpdateZPS. rewrite id_l. 
  triple_apply triple_setRegSep. 
Qed. 

Definition interpMemSpec (p pbase indexval:DWORD) (ms: MemSpec) :=
  let: mkMemSpec r ixspec offset := ms in
  if ixspec is Some(rix,sc) 
  then p = addB (addB pbase offset) (scaleBy sc indexval) /\\ r ~= pbase ** rix ~= indexval
  else p = addB pbase offset /\\ r ~= pbase.

Require Import tuple.
Definition interpDstSrc (v1 v2 pbase indexval:DWORD) (ds: DstSrc true) :=
  match ds with
  | DstSrcRR r1 r2 => 
    r1 ~= v1 ** 
    r2 ~= v2

  | DstSrcRM r1 ms => 
    let: mkMemSpec r ixspec offset := ms in
    r1 ~= v1 ** 
    r ~= pbase **
    if ixspec is Some(rix,sc)
    then rix ~= indexval ** addB (addB pbase offset) (scaleBy sc indexval) :-> v2
    else addB pbase offset :-> v2

  | DstSrcMR ms r2 => 
    let: mkMemSpec r ixspec offset := ms in
    r2 ~= v2 **
    r ~= pbase **
    if ixspec is Some(rix,sc)
    then rix ~= indexval ** addB (addB pbase offset) (scaleBy sc indexval) :-> v1
    else addB pbase offset :-> v1

  | DstSrcRI r1 c => 
    c == v2 /\\ r1 ~= v1

  | DstSrcMI ms c => 
    let: mkMemSpec r ixspec offset := ms in
    c == v2 /\\ 
    r ~= pbase **
    if ixspec is Some(rix,sc)
    then rix ~= indexval ** addB (addB pbase offset) (scaleBy sc indexval) :-> v1
    else addB pbase offset :-> v1
  end.

Lemma TripleEq (A:eqType) P c Q R (y:A) :
  (forall x, TRIPLE ((x = y /\\ P) ** R) (c x) Q) ->
  TRIPLE (P ** R) (c y) Q. 
Proof. 
move => T.
triple_apply  T.  
sbazooka. reflexivity. 
Qed.

(* Our first address-mode-generic rule *)
Lemma AND_rule (pbase indexval v1 v2 v: DWORD) (ds:DstSrc true) :
  andB v1 v2 = v ->  
   |--   basic (interpDstSrc v1 v2 pbase indexval ds ** OSZCP_Any)
            (BOP true (OP_AND) ds)
            (interpDstSrc v v2 pbase indexval ds **
             OSZCP false (msb v) (v == #0) false (lsb v)).
Proof.  
  move => E. 
  apply TRIPLE_basic => R. rewrite/evalInstr/evalDstSrc/interpDstSrc. 
  case: ds. 
  (* RR *)
  move => r1 r2. 
  triple_apply evalReg_rule. 
  rewrite /evalBinOp/evalLogicalOp assoc. 
  triple_apply evalReg_rule. rewrite assoc. 
  triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
  triple_apply triple_doSetFlagSep. rewrite assoc. 
  triple_apply triple_doSetFlagSep. rewrite assoc.
  triple_apply triple_doUpdateZPS. rewrite id_l. 
  rewrite E.   
  triple_apply triple_setRegSep. 
  (* RM *)
  move => r1 [base ixopt offset].
  rewrite /evalDstR. 
  triple_apply evalReg_rule.
  rewrite assoc. rewrite /evalMemSpec assoc. 
  case: ixopt => [[ixr sc] |]. 
(* Indexed *)
  + triple_apply triple_letGetRegSep. 
    rewrite assoc. 
    triple_apply triple_letGetRegSep. 
    rewrite id_l assoc.
    triple_apply triple_letGetDWORDSep. 
    rewrite /evalBinOp/evalLogicalOp. rewrite assoc. 
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    triple_apply triple_doSetFlagSep. rewrite assoc. 
    triple_apply triple_doSetFlagSep. rewrite assoc. 
    triple_apply triple_doUpdateZPS. rewrite id_l.
    rewrite E.  
    triple_apply triple_setRegSep. 
(* Non-indexed *)
  + triple_apply triple_letGetRegSep. 
    rewrite id_l assoc.
    triple_apply triple_letGetDWORDSep. 
    rewrite /evalBinOp/evalLogicalOp. rewrite assoc. 
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    triple_apply triple_doSetFlagSep. rewrite assoc. 
    triple_apply triple_doSetFlagSep. rewrite assoc. 
    triple_apply triple_doUpdateZPS. rewrite id_l.
    rewrite E.  
    triple_apply triple_setRegSep. 
  (* MR *)
  move => [base ixopt offset] r2.
  rewrite /evalDstM/evalMemSpec assoc. 
  case: ixopt => [[ixr sc] |]. 
(* Indexed *)
  + triple_apply triple_letGetRegSep. 
    rewrite assoc. 
    triple_apply triple_letGetRegSep. 
    rewrite id_l.
    triple_apply triple_letGetDWORDSep. 
    rewrite assoc. 
    triple_apply evalReg_rule.
    rewrite /evalBinOp/evalLogicalOp E assoc.
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    triple_apply triple_doSetFlagSep. rewrite assoc. 
    triple_apply triple_doSetFlagSep. rewrite assoc. 
    triple_apply triple_doUpdateZPS. rewrite id_l.
    triple_apply triple_setDWORDSep. 
(* Non-indexed *)
  + triple_apply triple_letGetRegSep. 
    rewrite id_l.
    triple_apply triple_letGetDWORDSep. 
    rewrite assoc. 
    triple_apply evalReg_rule. 
    rewrite /evalBinOp/evalLogicalOp E assoc. 
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    triple_apply triple_doSetFlagSep. rewrite assoc. 
    triple_apply triple_doSetFlagSep. rewrite assoc. 
    triple_apply triple_doUpdateZPS. rewrite id_l.
    triple_apply triple_setDWORDSep. 
  (* RI *)
  move => r1 c.
  rewrite /evalDstR/evalBinOp/evalLogicalOp. 
  rewrite /lpropand 2!sepSPA. apply triple_pre_existsSep => EQ. rewrite (eqP EQ).
  apply triple_post_existsSep => //. 
  triple_apply evalReg_rule. 
  rewrite E. 
  rewrite assoc.
  triple_apply triple_pre_introFlags => o sf zf cf pf. rewrite /OSZCP.
  triple_apply triple_doSetFlagSep. rewrite assoc. 
  triple_apply triple_doSetFlagSep. rewrite assoc. 
  triple_apply triple_doUpdateZPS. rewrite id_l.
  triple_apply triple_setRegSep.  

  (* MI *)
  move => [base ixopt offset] lit.
  rewrite /evalDstM/evalMemSpec assoc. 
  rewrite /lpropand 2!sepSPA. apply triple_pre_existsSep => EQ. rewrite (eqP EQ). 
  apply triple_post_existsSep => //. 
  case: ixopt => [[ixr sc] |]. 

(* Indexed *)
  + triple_apply triple_letGetRegSep. 
    rewrite assoc. 
    triple_apply triple_letGetRegSep. 
    rewrite id_l.
    triple_apply triple_letGetDWORDSep. 
    rewrite /evalBinOp/evalLogicalOp assoc E.
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    triple_apply triple_doSetFlagSep. rewrite assoc. 
    triple_apply triple_doSetFlagSep. rewrite assoc. 
    triple_apply triple_doUpdateZPS. rewrite id_l.
    triple_apply triple_setDWORDSep. 
(* Non-indexed *)
  + triple_apply triple_letGetRegSep. 
    rewrite id_l.
    triple_apply triple_letGetDWORDSep. 
    rewrite /evalBinOp/evalLogicalOp E assoc. 
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    triple_apply triple_doSetFlagSep. rewrite assoc. 
    triple_apply triple_doSetFlagSep. rewrite assoc. 
    triple_apply triple_doUpdateZPS. rewrite id_l.
    triple_apply triple_setDWORDSep. 
Qed.   

Lemma AND_RR_rule (r1 r2:Reg) v1 (v2:DWORD) v :
  andB v1 v2 = v ->
  |-- basic (r1~=v1 ** r2 ~= v2 ** OSZCP_Any)
            (and r1, r2)
            (r1~=v ** r2 ~= v2 **
             OSZCP false (msb v) (v == #0) false (lsb v)).
Proof.
  move => H.
  apply: basic_roc (AND_rule (pbase:=#0) (indexval:=#0) 
         (ds:=DstSrcRR true r1 r2) H); rewrite /interpDstSrc; sbazooka.
Qed.  

Lemma AND_RM_rule (pbase:BITS 32) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat) v :
  andB v1 v2 = v ->
  |-- basic (r1~=v1 ** OSZCP_Any)
            (and r1, [r2 + offset])
            (r1~=v ** OSZCP false (msb v) (v == #0) false (lsb v)) 
      @ (r2 ~= pbase ** pbase +# offset :-> v2).
Proof. move => H.
  autorewrite with push_at. 
  apply: basic_roc ((AND_rule (pbase:=pbase) (indexval:=#0) 
         (ds:=DstSrcRM true r1 (mkMemSpec r2 None #offset)) H)); rewrite /interpDstSrc; sbazooka. 
Qed. 

Lemma AND_RI_rule (r:Reg) v1 (v2:DWORD) v :
  andB v1 v2 = v ->
  |-- basic (r~=v1 ** OSZCP_Any)
            (and r, v2)
            (r~=v ** OSZCP false (msb v) (v == #0) false (lsb v)).
Proof. move => H.
  autorewrite with push_at. 
  apply: basic_roc ((AND_rule (pbase:=#0) (indexval:=#0) 
         (ds:=DstSrcRI true r v2) H)); rewrite /interpDstSrc. 
  + sbazooka.  
  + ssimpl. by apply lpropandL. 
Qed. 

 
Lemma OR_RM_rule (pd:BITS 32) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat) v :
  orB v1 v2 = v ->
  |-- basic (r1~=v1 ** r2 ~= pd ** pd +# offset :-> v2 ** OSZCP_Any)
            (or r1, [r2 + offset])
            (r1~=v ** r2 ~= pd ** pd +# offset :-> v2 **
             OSZCP false (msb v) (v == #0) false (lsb v)).
Proof.
  move => E. apply TRIPLE_basic => R.
  rewrite /evalInstr/evalDstSrc/evalDstR /RegMemPairToDstSrc.
  triple_apply evalReg_rule. rewrite /evalBinOp/evalLogicalOp assoc.
  triple_apply evalMemSpec_rule. rewrite assoc. 
  triple_apply triple_letGetDWORDSep. rewrite assoc.
  triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
  triple_apply triple_doSetFlagSep. rewrite assoc. 
  triple_apply triple_doSetFlagSep. rewrite E assoc.
  triple_apply triple_doUpdateZPS. rewrite id_l. 
  triple_apply triple_setRegSep. 
Qed. 

Lemma XOR_RM_rule (pd:BITS 32) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat) v :
  xorB v1 v2 = v ->
  |-- basic (r1~=v1 ** r2 ~= pd ** pd +# offset :-> v2 ** OSZCP_Any)
            (xor r1, [r2 + offset])
            (r1~=v ** r2 ~= pd ** pd +# offset :-> v2 **
             OSZCP false (msb v) (v == #0) false (lsb v)).
Proof.
  (* Copy-paste of OR_RM_rule proof *)
  move => E. apply TRIPLE_basic => R.
  rewrite /evalInstr/evalDstSrc/evalDstR /RegMemPairToDstSrc.
  triple_apply evalReg_rule. rewrite /evalBinOp/evalLogicalOp assoc.
  triple_apply evalMemSpec_rule. rewrite assoc. 
  triple_apply triple_letGetDWORDSep. rewrite assoc.
  triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
  triple_apply triple_doSetFlagSep. rewrite assoc. 
  triple_apply triple_doSetFlagSep. rewrite E assoc.
  triple_apply triple_doUpdateZPS. rewrite id_l. 
  triple_apply triple_setRegSep. 
Qed. 

Lemma SUB_RR_rule (r1 r2:Reg) v1 (v2:DWORD) carry v:
  sbbB false v1 v2 = (carry,v) ->
  |-- basic (r1~=v1 ** r2~=v2 ** OSZCP_Any) (sub r1, r2)
            (r1~=v  ** r2~=v2 **
             OSZCP (computeOverflow v1 v2 v) (msb v) (v == #0) carry (lsb v)).
Proof.
  move => E. apply TRIPLE_basic => R.
  rewrite /evalInstr/evalDstSrc/evalDstR /RegMemPairToDstSrc.
  triple_apply evalReg_rule. rewrite assoc.
  triple_apply evalReg_rule.
  rewrite /evalBinOp/evalArithOpNoCarry.
  triple_apply triple_pre_introFlags => o s z c p. rewrite /OSZCP.
  rewrite E assoc. 
  triple_apply triple_doSetFlagSep. rewrite assoc. 
  triple_apply triple_doSetFlagSep. rewrite assoc.
  triple_apply triple_doUpdateZPS. rewrite id_l. 
  triple_apply triple_setRegSep. 
Qed. 

Lemma SUB_RI_rule (r1:Reg) v1 (v2:DWORD) carry v:
  sbbB false v1 v2 = (carry,v) ->
  |-- basic (r1~=v1 ** OSZCP_Any) (sub r1, v2)
            (r1~=v **
             OSZCP (computeOverflow v1 v2 v) (msb v) (v == #0) carry (lsb v)).
Proof.
  (* Copy-paste of ADD_RI_rule proof *)
  move => E. apply TRIPLE_basic => R.
  rewrite /evalInstr/evalDstSrc/evalDstR /RegMemPairToDstSrc.
  triple_apply evalReg_rule. 
  rewrite /evalBinOp/evalArithOpNoCarry.
  triple_apply triple_pre_introFlags => o s z c p. rewrite /OSZCP.
  rewrite E assoc. 
  triple_apply triple_doSetFlagSep. rewrite assoc. 
  triple_apply triple_doSetFlagSep. rewrite assoc.
  triple_apply triple_doUpdateZPS. rewrite id_l. 
  triple_apply triple_setRegSep. 
Qed. 


Lemma CMP_RI_rule (r1:Reg) v1 (v2:DWORD) carry res:
  sbbB false v1 v2 = (carry, res) ->
  |-- basic (r1 ~= v1 ** OSZCP_Any) (cmp r1, v2)
            (r1 ~= v1 ** OSZCP (computeOverflow v1 v2 res) (msb res)
                         (res == #0) carry (lsb res)).
Proof.
  move => E. apply TRIPLE_basic => R.
  rewrite /evalInstr/evalDstSrc/evalDstR /RegMemPairToDstSrc.
  triple_apply evalReg_rule. 
  rewrite /evalBinOp/evalArithOpNoCarry E assoc.
  triple_apply triple_pre_introFlags => o s z c p. rewrite /OSZCP.
  triple_apply triple_doSetFlagSep. rewrite assoc. 
  triple_apply triple_doSetFlagSep. rewrite assoc.
  triple_apply triple_doUpdateZPS. rewrite id_l. 
  triple_apply triple_skip. 
Qed. 


Lemma CMP_RM_rule (pd:BITS 32) (r1 r2:Reg) offset (v1 v2:DWORD) carry res :
  sbbB false v1 v2 = (carry, res) ->
  |-- basic (r1 ~= v1 ** r2 ~= pd ** pd +# offset :-> v2 ** OSZCP_Any)
            (cmp r1, [r2+offset])
            (r1 ~= v1 ** r2 ~= pd ** pd +# offset :-> v2 **
             OSZCP (computeOverflow v1 v2 res) (msb res)
                   (res == #0) carry (lsb res)).
Proof.
  move => E. apply TRIPLE_basic => R.
  rewrite /evalInstr /evalDstSrc/evalDstR /RegMemPairToDstSrc.
  triple_apply evalReg_rule.
  rewrite /evalBinOp/evalArithOpNoCarry/evalMemSpec assoc assoc.
  triple_apply evalReg_rule. rewrite id_l assoc. 
  triple_apply triple_letGetDWORDSep. rewrite E assoc.
  triple_apply triple_pre_introFlags => o s z c p. rewrite /OSZCP.
  triple_apply triple_doSetFlagSep. rewrite assoc. 
  triple_apply triple_doSetFlagSep. rewrite assoc.
  triple_apply triple_doUpdateZPS. triple_apply triple_skip. 
Qed. 


Lemma CMP_MR_rule (pd:BITS 32) (r1 r2:Reg) offset (v1 v2:DWORD) carry res:
  sbbB false v2 v1 = (carry, res) ->
  |-- basic (r1 ~= v1 ** r2 ~= pd ** pd +# offset :-> v2 ** OSZCP_Any)
            (cmp [r2+offset], r1)
            (r1 ~= v1 ** r2 ~= pd ** pd +# offset :-> v2 **
             OSZCP (computeOverflow v2 v1 res) (msb res)
                   (res == #0) carry (lsb res)).
Proof.
  move => E. apply TRIPLE_basic => R.
  rewrite /evalInstr /evalDstSrc /RegMemPairToDstSrc.
  triple_apply evalMemSpec_rule. 
  triple_apply triple_letGetDWORDSep. rewrite assoc.
  triple_apply evalReg_rule. rewrite /evalBinOp/evalArithOpNoCarry E assoc. 
  triple_apply triple_pre_introFlags => o s z c p. rewrite /OSZCP.
  triple_apply triple_doSetFlagSep. rewrite assoc. 
  triple_apply triple_doSetFlagSep. rewrite assoc.
  triple_apply triple_doUpdateZPS.
  triple_apply triple_skip. 
Qed. 

Lemma CMP_RR_rule (r1 r2:Reg) v1 (v2:DWORD) carry res:
  sbbB false v1 v2 = (carry, res) ->
  |-- basic (r1 ~= v1 ** r2 ~= v2 ** OSZCP_Any) (cmp r1, r2)
            (r1 ~= v1 ** r2 ~= v2 **
              OSZCP (computeOverflow v1 v2 res) (msb res)
                    (res == #0) carry (lsb res)).
Proof.
  move => E. apply TRIPLE_basic => R.
  rewrite /evalInstr/evalDstSrc/evalDstR /RegMemPairToDstSrc.
  triple_apply evalReg_rule. rewrite assoc.
  triple_apply evalReg_rule.
  rewrite /evalBinOp/evalArithOpNoCarry E assoc.
  triple_apply triple_pre_introFlags => o s z c p. rewrite /OSZCP.
  triple_apply triple_doSetFlagSep. rewrite assoc. 
  triple_apply triple_doSetFlagSep. rewrite assoc.
  triple_apply triple_doUpdateZPS. rewrite id_l. 
  triple_apply triple_skip. 
Qed.

Lemma TEST_self_rule (r:Reg) (v:DWORD) :
  |-- basic (r ~= v ** OSZCP_Any) (test r, r)
            (r ~= v ** OSZCP false (msb v) (v == #0) false (lsb v)).
Proof.
  apply TRIPLE_basic => R.
  rewrite /evalInstr/evalDst/evalDstR/evalRegImm.
  triple_apply evalReg_rule. rewrite assoc. 
  triple_apply evalReg_rule. rewrite /evalBinOp/evalArithOp assoc andBB.
  triple_apply triple_pre_introFlags => o s z c p. rewrite /OSZCP.
  triple_apply triple_doSetFlagSep. rewrite assoc.
  triple_apply triple_doSetFlagSep. rewrite assoc.
  triple_apply triple_doUpdateZPS.
  triple_apply triple_skip. 
Qed. 


(* Lazy man's proof *)
Lemma SmallCount : forall count, count < 32 -> toNat (n:=8) (andB #x"1f" #count) = count. 
Proof. do 32 case => //. 
Qed. 

Lemma SHL_RI_rule (r:Reg) (v:DWORD) (count:nat):
  count < 32 -> 
  |-- basic (r~=v ** OSZCP_Any) (shl r, count)
            (r~=iter count shlB v ** OSZCP_Any).
Proof.
  move => BOUND. 
  apply TRIPLE_basic => R.
  rewrite /evalInstr/evalDst/evalDstR /RegMemPairToDstSrc.
  triple_apply evalReg_rule. 
  rewrite /evalShiftCount/evalShiftOp assoc id_l.
  rewrite (SmallCount BOUND). 
  case E: count => [| count'].   
  + rewrite id_l. replace (iter _ _ v) with v by done. 
    triple_apply triple_setRegSep. 

  + 
  rewrite assoc.      
  triple_apply triple_pre_introFlags => o s z c p. 
  rewrite /OSZCP_Any/OSZCP.
  rewrite id_l assoc.
  triple_apply triple_doSetFlagSep. rewrite assoc. 
  case E': count' => [| count''].     
  + triple_apply triple_doSetFlagSep. rewrite id_l. 
    triple_apply triple_setRegSep. rewrite dropmsb_iter_shlB.
    rewrite /flagAny. sbazooka.  
  + triple_apply triple_doForgetFlagSep. rewrite id_l. 
    triple_apply triple_setRegSep.
    rewrite dropmsb_iter_shlB.     
    rewrite /flagAny. sbazooka. 
Qed. 

Lemma SHR_RI_rule (r:Reg) (v:DWORD) (count:nat):
  count < 32 -> 
  |-- basic (r~=v ** OSZCP_Any) (shr r, count)
            (r~=iter count shrB v ** OSZCP_Any).
Proof.
  move => BOUND. 
  apply TRIPLE_basic => R.
  rewrite /evalInstr/evalDst/evalDstR /RegMemPairToDstSrc.
  triple_apply evalReg_rule. 
  rewrite /evalShiftCount/evalShiftOp assoc id_l.
  rewrite (SmallCount BOUND). 
  case E: count => [| count'].   
  + rewrite id_l. replace (iter _ _ v) with v by done. 
    triple_apply triple_setRegSep. 

  + 
  rewrite assoc.      
  triple_apply triple_pre_introFlags => o s z c p. 
  rewrite /OSZCP_Any/OSZCP.
  rewrite id_l assoc. 
  triple_apply triple_doSetFlagSep. rewrite assoc. 
  case E': count' => [| count''].     
  + triple_apply triple_doSetFlagSep. rewrite id_l. 
    triple_apply triple_setRegSep. rewrite droplsb_iter_shrB.
    rewrite /flagAny. sbazooka.  
  + triple_apply triple_doForgetFlagSep. rewrite id_l. 
    triple_apply triple_setRegSep.
    rewrite droplsb_iter_shrB.     
    rewrite /flagAny. sbazooka. 
Qed. 

(*---------------------------------------------------------------------------
    Stack operations
  ---------------------------------------------------------------------------*)

(* Push register *)
Lemma PUSH_R_rule (r:Reg) sp (v w:DWORD) :
  |-- basic (r ~= v ** ESP ~= sp    ** sp-#4 :-> w) (PUSH r)
            (r ~= v ** ESP ~= sp-#4 ** sp-#4 :-> v).
Proof.
  apply TRIPLE_basic => R.
  rewrite /evalInstr/evalSrc/evalPush. 
  triple_apply evalReg_rule.
  triple_apply triple_letGetRegSep. 
  triple_apply triple_doSetRegSep. 
  triple_apply triple_setDWORDSep. 
Qed. 

(* Push immediate *)
Lemma PUSH_I_rule (sp v w:DWORD) :
  |-- basic (ESP ~= sp    ** sp-#4 :-> w) (PUSH v)
            (ESP ~= sp-#4 ** sp-#4 :-> v).
Proof.
  apply TRIPLE_basic => R.
  rewrite /evalInstr/evalSrc/evalPush.
  rewrite id_l. 
  triple_apply triple_letGetRegSep. 
  triple_apply triple_doSetRegSep. 
  triple_apply triple_setDWORDSep. 
Qed. 

(* Pop register *)
Lemma POP_R_rule (r:Reg) (sp:BITS 32) (v w:DWORD):
  |-- basic (r ~= v ** ESP ~= sp    ** sp:->w) (pop r)
            (r ~= w ** ESP ~= sp+#4 ** sp:->w).
Proof.
  apply TRIPLE_basic => R.
  rewrite /evalInstr /evalDst /evalDstR.
  triple_apply triple_letGetRegSep. rewrite assoc.
  triple_apply triple_letGetRegSep. rewrite assoc. 
  triple_apply triple_letGetDWORDSep.
  triple_apply triple_doSetRegSep. 
  triple_apply triple_setRegSep. 
Qed. 


(*---------------------------------------------------------------------------
    Now, rules that involve control-flow.
  ---------------------------------------------------------------------------*)

(* unconditional jump *)
Lemma JMP_I_rule addr (p q: DWORD) :
  |-- (|> safe @ (EIP ~= addr) -->> safe @ (EIP ~= p)) <@
        (p -- q :-> jmp addr).
Proof.
  rewrite -[EIP~=p]empSPR. apply TRIPLE_safe => R.
  rewrite /evalInstr/evalSrc. rewrite id_l.
  triple_apply triple_setRegSep. 
Qed. 

Lemma JMP_R_rule (r:Reg) addr (p q: DWORD) :
  |-- (|> safe @ (EIP ~= addr ** r ~= addr) -->> safe @ (EIP ~= p ** r ~= addr)) <@
        (p -- q :-> JMP (SrcR r)).
Proof.
  apply TRIPLE_safe => R.
  rewrite /evalInstr/evalSrc /evalReg. rewrite assoc.
  triple_apply triple_letGetRegSep. rewrite id_l.
  triple_apply triple_setRegSep. 
Qed. 

Definition ConditionIs cc cv :=
  match cc with
  | CC_O => flagIs OF cv
  | CC_B => flagIs CF cv
  | CC_Z => flagIs ZF cv
  | CC_S => flagIs SF cv
  | CC_P => flagIs PF cv
  | CC_BE => Exists cf, Exists zf, cv = cf || zf /\\ flagIs CF cf ** flagIs ZF zf
  | CC_L => Exists sf, Exists f, cv = xorb sf f /\\ flagIs SF sf ** flagIs OF f
  | CC_LE => Exists sf, Exists f, Exists zf, cv = (xorb sf f) || zf /\\
               flagIs SF sf ** flagIs OF f ** flagIs ZF zf
  end.

Lemma triple_letGetCondition cc (v:bool) (P Q: SPred) c: 
  TRIPLE (ConditionIs cc v ** P) (c v) Q -> 
  TRIPLE (ConditionIs cc v ** P) (bind (evalCondition cc) c) Q.
Proof. 
  rewrite /evalCondition /ConditionIs => H. destruct cc.
  - (* CC_O *)
    triple_apply triple_letGetFlag; by [ssimpl|].
  - (* CC_C *)
    triple_apply triple_letGetFlag; by [ssimpl|].
  - (* CC_Z *)
    triple_apply triple_letGetFlag; by [ssimpl|].
  - (* CC_BE *)
    rewrite assoc.
    apply triple_pre_existsSep => fc. triple_apply triple_letGetFlag.
    - by sbazooka.
    rewrite assoc.
    apply triple_pre_existsSep => fz. triple_apply triple_letGetFlag.
    - by sbazooka.
    rewrite /lpropand. apply triple_pre_existsSep => Hv. inversion Hv. 
    subst v. 
    rewrite id_l. eapply triple_roc_pre; last apply H. by sbazooka.
  - (* CC_S *)
    triple_apply triple_letGetFlag; by [ssimpl|].
  - (* CC_P *)
    triple_apply triple_letGetFlag; by [ssimpl|].
  - (* CC_L *)
    rewrite assoc.
    apply triple_pre_existsSep => fs. triple_apply triple_letGetFlag.
    - by sbazooka.
    rewrite assoc.
    apply triple_pre_existsSep => fo. triple_apply triple_letGetFlag.
    - by sbazooka.
    rewrite /lpropand. apply triple_pre_existsSep => Hv. inversion Hv. subst v.
    rewrite id_l. eapply triple_roc_pre; last apply H. by sbazooka.
  - (* CC_LE *)
    rewrite assoc.
    apply triple_pre_existsSep => fs. triple_apply triple_letGetFlag.
    - by sbazooka.
    rewrite assoc.
    apply triple_pre_existsSep => fo. triple_apply triple_letGetFlag.
    - by sbazooka.
    rewrite assoc.
    apply triple_pre_existsSep => fz. triple_apply triple_letGetFlag.
    - by sbazooka.
    rewrite /lpropand. apply triple_pre_existsSep => Hv. inversion Hv. subst v.
    rewrite id_l. eapply triple_roc_pre; last apply H. by sbazooka.
Qed. 

(* For convenience, the ~~b branch is not under a |> operator since q will
   never be equal to p, and thus there is no risk of recursion. *)
Lemma JCC_rule addr cc cv (b:bool) (p q: DWORD) :
  |-- (
      |> safe @ (b == cv /\\ EIP ~= addr ** ConditionIs cc b) //\\
         safe @ (b == ~~cv /\\ EIP ~= q ** ConditionIs cc b) -->>
      safe @ (EIP ~= p ** ConditionIs cc b)
    ) <@ (p -- q :-> JCC cc cv addr).
Proof.
  Import Setoid.
  rewrite ->(@spec_later_weaken (safe @ (b == ~~ cv /\\ EIP~=q ** ConditionIs cc b))).
  rewrite <-spec_later_and. rewrite ->spec_at_and_or; last apply _.
  apply TRIPLE_safe => R. rewrite /evalInstr.
  triple_apply triple_letGetCondition.
  replace (b == ~~cv) with (~~(b == cv)); last first.
  - case: b; case: cv; reflexivity.
  case: (b == cv).
  - triple_apply triple_doGetReg. 
    triple_apply triple_setRegSep.
    apply: lorR1. by ssplit.
  - triple_apply triple_skip. 
    apply: lorR2. by sbazooka.
Qed.

(* Special case for the JZ instruction *)
Lemma JZ_rule addr (b:bool) (p q: DWORD) :
  |-- (
      |> safe @ (b == true  /\\ EIP ~= addr ** flagIs ZF b) //\\
         safe @ (b == false /\\ EIP ~= q ** flagIs ZF b) -->>
      safe @ (EIP ~= p ** flagIs ZF b)
    ) <@ (p -- q :-> jz addr).
Proof. apply JCC_rule. Qed.

(* Special case for the JC instruction *)
Lemma JC_rule addr (b:bool) (p q: DWORD) :
  |-- (
      |> safe @ (b == true  /\\ EIP ~= addr ** flagIs CF b) //\\
         safe @ (b == false /\\ EIP ~= q ** flagIs CF b) -->>
      safe @ (EIP ~= p ** flagIs CF b)
    ) <@ (p -- q :-> jc addr).
Proof. apply JCC_rule. Qed.

(* TODO: JCC_Z_rule and JCC_C_rule are missing. Are they needed? *)

Lemma RET_rule p' (sp:BITS 32) (offset:WORD) (p q: DWORD) :
  let sp':BITS 32 := addB (sp+#4) (zero 16 ## offset) in
  |-- (
      |> safe @ (EIP ~= p' ** ESP ~= sp' ** sp :-> p') -->>
         safe @ (EIP ~= p  ** ESP ~= sp  ** sp :-> p')
    ) <@ (p -- q :-> RET offset).
Proof.
  apply TRIPLE_safe => R.
  rewrite /evalInstr.
  triple_apply triple_letGetRegSep. 
  triple_apply triple_letGetDWORDSep.
  triple_apply triple_doSetRegSep.
  triple_apply triple_setRegSep.
Qed.

Lemma CALL_R_rule (p':DWORD) {w:DWORD} (r:Reg) (sp:BITS 32) (p q: DWORD) :
  |-- (
      |> safe @ (EIP ~= p' ** r~=p' ** ESP~=sp-#4 ** sp-#4 :-> q) -->>
         safe @ (EIP ~= p  ** r~=p' ** ESP~=sp    ** sp-#4 :-> w)
    ) <@ (p -- q :-> CALL r).
Proof.
  apply TRIPLE_safe => R.
  rewrite /evalInstr /evalRegMem /evalReg /evalPush. 
  triple_apply triple_letGetRegSep. rewrite assoc.
  triple_apply triple_letGetRegSep. rewrite id_l.
  triple_apply triple_doSetRegSep.
  triple_apply triple_letGetRegSep.
  triple_apply triple_doSetRegSep.
  triple_apply triple_setDWORDSep.
Qed.

