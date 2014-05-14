(*===========================================================================
    Bitwise codecs used in instruction encoding and decoding

    See Intel IA-32 Software Developers Manual, Volume 2, Appendix B
    
  ===========================================================================*)
Require Import ssreflect ssrfun ssrbool ssrnat seq tuple eqtype.
Require Import bitsrep bitsprops reg instr emb.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition allScales := [tuple S1; S2; S4; S8].
Definition decScale (b: BITS 2) := tnth allScales (toZp b). 
Definition encScale r : BITS 2 :=  
  match r with S1 => #b"00" | S2 => #b"01" | S4 => #b"10" | S8 => #b"11" end.
Lemma encScaleK : cancel encScale decScale. Proof. by case. Qed. 
Canonical Structure ScaleEqMixin := CanEqMixin encScaleK.  
Canonical Structure ScaleEqType := Eval hnf in EqType _ ScaleEqMixin.
Instance scaleEMB: EMB _ _ := Emb encScaleK. 

Definition allNonSPReg := [tuple Some EAX; Some ECX; Some EDX; Some EBX; 
                                 None;     Some EBP; Some ESI; Some EDI].

Definition decNonSPReg (b: BITS 3) := tnth allNonSPReg (toZp b). 
Definition encNonSPReg r : BITS 3 :=
  match r with
  | EAX => #b"000"
  | ECX => #b"001"
  | EDX => #b"010"
  | EBX => #b"011"
  | EBP => #b"101"
  | ESI => #b"110"
  | EDI => #b"111"
  end.
Lemma encNonSPRegK : pcancel encNonSPReg decNonSPReg. Proof. by case. Qed. 
Canonical Structure NonSPRegEqMixin := PcanEqMixin encNonSPRegK.  
Canonical Structure NonSPRegEqType := Eval hnf in EqType _ NonSPRegEqMixin.
Instance NonSPRegEMB: EMB _ _ := PEmb encNonSPRegK. 
Coercion injNonSPReg := (@inj _ _ NonSPRegEMB).


Definition allReg := [tuple EAX:Reg;ECX:Reg;EDX:Reg;EBX:Reg;ESP:Reg;EBP:Reg;ESI:Reg;EDI:Reg].
Definition decReg (b: BITS 3) := tnth allReg (toZp b). 
Definition encReg r : BITS 3 :=
  match r with
  | ESP => #b"100"
  | nonSPReg r => encNonSPReg r 
  end.
Lemma encRegK : cancel encReg decReg. Proof. by case => //; case => //. Qed. 
Canonical Structure RegEqMixin := CanEqMixin encRegK.  
Canonical Structure RegEqType := Eval hnf in EqType _ RegEqMixin.
Instance RegEMB : EMB _ _ := Emb encRegK.
Coercion injReg := (@inj _ _ RegEMB).

Definition allBYTEReg := [tuple AL;CL;DL;BL;AH;CH;DH;BH].
Definition decBYTEReg (b: BITS 3) := tnth allBYTEReg (toZp b). 
Definition encBYTEReg r : BITS 3 :=
  match r with
  | AL => #b"000"
  | CL => #b"001"
  | DL => #b"010"
  | BL => #b"011"
  | AH => #b"100"
  | CH => #b"101"
  | DH => #b"110"
  | BH => #b"111"
  end.
Lemma encBYTERegK : cancel encBYTEReg decBYTEReg. Proof. by case => //; case => //. Qed. 
Canonical Structure BYTERegEqMixin := CanEqMixin encBYTERegK.  
Canonical Structure BYTERegEqType := Eval hnf in EqType _ BYTERegEqMixin.
Instance BYTERegEMB : EMB _ _ := Emb encBYTERegK.
Coercion injBYTEReg := (@inj _ _ BYTERegEMB).

Definition decDWORDorBYTEReg dword :=
  if dword as dword return BITS 3 -> DWORDorBYTEReg dword then decReg else decBYTEReg.
Definition encDWORDorBYTEReg dword : DWORDorBYTEReg dword -> BITS 3 :=
  if dword as dword return DWORDorBYTEReg dword -> BITS 3 then encReg else encBYTEReg.
Lemma encDWORDorBYTERegK dword : cancel (@encDWORDorBYTEReg dword) (decDWORDorBYTEReg dword). 
Proof. destruct dword; [apply encRegK | apply encBYTERegK]. Qed. 

Instance DWORDorBYTERegEMB dword : EMB _ _ := Emb (@encDWORDorBYTERegK dword). 
Coercion injDWORDorBYTEReg dword := (@inj _ _ (DWORDorBYTERegEMB dword)).

(* It's important that these are notations so we can pattern-match against them *)
Notation DISP0  := (#b"00") (only parsing).
Notation DISP8  := (#b"01") (only parsing).
Notation DISP32 := (#b"10") (only parsing).
Notation MODREG := (#b"11") (only parsing).

Notation SIBRM  := (#b"100") (only parsing).


Notation INCPREF    := (#b"01000") (only parsing).
Notation DECPREF    := (#b"01001") (only parsing).
Notation PUSHPREF   := (#b"01010") (only parsing).
Notation POPPREF    := (#b"01011") (only parsing).
Notation MOVIMMPREF := (#b"10111") (only parsing).

Notation JCC8PREF   := (#b"0111") (only parsing).
Notation JCC32PREF  := (#b"1000") (only parsing).
Notation BITOPPREF  := (#b"101") (only parsing).
Notation BITIMMSUFF := (#b"11010") (only parsing).
Notation BITOPSUFF  := (#b"011") (only parsing).

(* Condition code encoding *)
Definition allCondition := [tuple CC_O; CC_B; CC_Z; CC_BE; CC_S; CC_P; CC_L; CC_LE].
Definition decCondition (b: BITS 3) := tnth allCondition (toZp b). 
Definition encCondition c : BITS 3 :=
  match c with
  | CC_O         => #b"000"
  | CC_B         => #b"001"
  | CC_Z         => #b"010"
  | CC_BE        => #b"011"
  | CC_S         => #b"100"
  | CC_P         => #b"101"
  | CC_L         => #b"110"
  | CC_LE        => #b"111"
  end.
Lemma encConditionK : cancel encCondition decCondition. Proof. by case. Qed. 
Instance ConditionEMB: EMB _ _ := Emb encConditionK. 

(* Binary operation encoding *)
Definition allBinOp := [tuple OP_ADD; OP_OR; OP_ADC; OP_SBB; OP_AND; OP_SUB; OP_XOR; OP_CMP].
Definition decBinOp (b: BITS 3) := tnth allBinOp (toZp b).
Definition encBinOp (op: BinOp) :=
  match op with
  | OP_ADD => #b"000"
  | OP_OR  => #b"001"
  | OP_ADC => #b"010"
  | OP_SBB => #b"011"
  | OP_AND => #b"100"
  | OP_SUB => #b"101"
  | OP_XOR => #b"110"
  | OP_CMP => #b"111"
  end.
Lemma encBinOpK : cancel encBinOp decBinOp. Proof. by case. Qed. 
Instance BinOpEMB: EMB _ _ := Emb encBinOpK. 

(* Bit operation encoding *)
Definition allBitOp := [tuple OP_BT; OP_BTS; OP_BTR; OP_BTC].
Definition decBitOp (b: BITS 2) := tnth allBitOp (toZp b). 
Definition encBitOp (op: BitOp) :=
  match op with
  | OP_BT  => #b"00"
  | OP_BTS => #b"01"
  | OP_BTR => #b"10"
  | OP_BTC => #b"11"
  end.
Lemma encBitOpK : cancel encBitOp decBitOp. Proof. by case. Qed.
Instance BitOpEMB: EMB _ _ := Emb encBitOpK. 

(* Shift operation encoding *)
Definition allShiftOp := [tuple OP_ROL; OP_ROR; OP_RCL; OP_RCR; OP_SHL; OP_SHR; OP_SAL; OP_SAR].
Definition decShiftOp (b: BITS 3) := tnth allShiftOp (toZp b).
Definition encShiftOp (op: ShiftOp) :=
  match op with
  | OP_ROL => #b"000"
  | OP_ROR => #b"001"
  | OP_RCL => #b"010"
  | OP_RCR => #b"011"
  | OP_SHL => #b"100"
  | OP_SHR => #b"101"
  | OP_SAL => #b"110"
  | OP_SAR => #b"111"
  end.
Lemma encShiftOpK : cancel encShiftOp decShiftOp. Proof. by case. Qed.
Instance ShiftOpEMB: EMB _ _ := Emb encShiftOpK. 


