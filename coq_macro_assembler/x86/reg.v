(*===========================================================================
    Model for x86 registers
    Note that the EFL register (flags) is treated separately.
  ===========================================================================*)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype tuple.
Require Import bitsrep.

(* General purpose registers, excluding ESP *)
(*=NonSPReg *)
Inductive NonSPReg := 
| EAX | EBX | ECX | EDX | ESI | EDI | EBP.
(*=End *)
Definition NonSPRegToNat r :=  
  match r with EAX => 0 | ECX => 1 | EDX => 2 | EBX => 3 | EBP => 5 | ESI => 6 | EDI => 7 end.
Lemma NonSPRegToNat_inj : injective NonSPRegToNat. Proof. by case => //; case => //. Qed. 
Canonical Structure NonSPRegEqMixin := InjEqMixin NonSPRegToNat_inj.
Canonical Structure NonSPRegEqType := Eval hnf in EqType _ NonSPRegEqMixin.

(* General purpose registers, including ESP *)
(*=Reg *)
Inductive Reg :=
| nonSPReg :> NonSPReg -> Reg
| ESP.
(*=End *)
Definition RegToNat r :=  match r with | ESP => 4 | nonSPReg r => NonSPRegToNat r end.
Lemma RegToNat_inj : injective RegToNat. 
Proof. case => //; case => //; case => //; case => //. Qed. 
Canonical Structure RegEqMixin := InjEqMixin RegToNat_inj.
Canonical Structure RegEqType := Eval hnf in EqType _ RegEqMixin.
  
(* All registers, including EIP but excluding EFL *)
(*=AnyReg *)
Inductive AnyReg :=
| regToAnyReg :> Reg -> AnyReg
| EIP. 
(*=End *)
Definition AnyRegToNat r :=  match r with | EIP => 8 | regToAnyReg r => RegToNat r end.
Lemma AnyRegToNat_inj : injective AnyRegToNat. 
Proof. case => //; case => //; case => //; case => //; case => //; case => //. Qed. 
Canonical Structure AnyRegEqMixin := InjEqMixin AnyRegToNat_inj.
Canonical Structure AnyRegEqType := Eval hnf in EqType _ AnyRegEqMixin.

(* Segment registers *)
Inductive SegReg := CS | DS | SS | ES | FS | GS.

(* Standard numbering of registers *)
Definition natToReg n : option Reg :=
  match n return option Reg with 
  | 0 => Some (EAX:Reg) 
  | 1 => Some (ECX:Reg)
  | 2 => Some (EDX:Reg) 
  | 3 => Some (EBX:Reg)
  | 4 => Some (ESP:Reg)
  | 5 => Some (EBP:Reg)
  | 6 => Some (ESI:Reg)
  | 7 => Some (EDI:Reg)
  | _ => None
  end.  

Lemma roundtripReg : forall r, natToReg (RegToNat r) = Some r. 
Proof. case. by case. done. Qed.

(* Reg is a choiceType and a countType *)
Definition Reg_countMixin := CountMixin roundtripReg. 
Definition Reg_choiceMixin := CountChoiceMixin Reg_countMixin.
Canonical Reg_choiceType :=  Eval hnf in ChoiceType _ Reg_choiceMixin.
Canonical Reg_countType  :=  Eval hnf in CountType _ Reg_countMixin.

(* Reg is a finType *)
Lemma Reg_enumP : 
  Finite.axiom [:: EAX:Reg; EBX:Reg; ECX:Reg; EDX:Reg; ESI:Reg; EDI:Reg; EBP:Reg; ESP].
Proof. case;  [by case | done]. Qed. 

Definition Reg_finMixin := Eval hnf in FinMixin Reg_enumP.
Canonical Reg_finType   := Eval hnf in FinType _ Reg_finMixin.  

(* Standard numbering of registers *)
Definition natToAnyReg n :=
  match natToReg n with
  | Some r => Some (regToAnyReg r)
  | None => match n with 8 => Some EIP | _ => None end
  end.

Lemma roundtripAnyReg : forall r, natToAnyReg (AnyRegToNat r) = Some r. 
Proof. case. case; [case; by constructor | done]. done. Qed. 

(* AnyReg is a choiceType and a countType *)
Definition AnyReg_countMixin := CountMixin roundtripAnyReg. 
Definition AnyReg_choiceMixin := CountChoiceMixin AnyReg_countMixin.
Canonical AnyReg_choiceType := Eval hnf in ChoiceType _ AnyReg_choiceMixin.
Canonical AnyReg_countType  := Eval hnf in CountType  _ AnyReg_countMixin.

(* AnyReg is a finType *)
Lemma AnyReg_enumP : 
  Finite.axiom [:: EAX:AnyReg; EBX:AnyReg; ECX:AnyReg; 
                   EDX:AnyReg; ESI:AnyReg; EDI:AnyReg; EBP:AnyReg; ESP:AnyReg; EIP].
Proof. case; [case; [case; done | done] | done]. Qed. 

Definition AnyReg_finMixin := Eval hnf in FinMixin AnyReg_enumP.
Canonical AnyReg_finType :=  Eval hnf in FinType _ AnyReg_finMixin.  

