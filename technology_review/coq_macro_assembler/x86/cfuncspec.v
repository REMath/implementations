(*===========================================================================
  Specification and proof for C calling conventions
  ===========================================================================*)
Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq fintype tuple.
Require Import procstate procstatemonad bitsrep bitsops bitsprops bitsopsprops.
Require Import SPred septac spec safe basic program macros call.
Require Import instr instrsyntax decinstr instrrules reader pointsto cursor spectac.
Require Import NaryFunctions.
Require Import cfunc.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope instr_scope.

(* Create special purpose lemma just to use sbazooka below *)
Lemma SAFEY (P P' Q Q': SPred) : 
  P |-- P' ->
  Q' |-- Q ->
  safe @ P -->> |>safe @ Q |--
  safe @ P' -->> |>safe @ Q'.
Proof. move => H1 H2. 
setoid_rewrite H1. 
setoid_rewrite H2.
done.
Qed.

Lemma SAFEY2 (P P' Q Q': SPred) : 
  P |-- P' ->
  Q' |-- Q ->
  safe @ P -->> safe @ Q |--
  safe @ P' -->> safe @ Q'.
Proof. move => H1 H2. 
setoid_rewrite H1. 
setoid_rewrite H2.
done.
Qed.


(*---------------------------------------------------------------------------
    Calling-convention-independent specification of function behaviour
  ---------------------------------------------------------------------------*)

(* Specification for a given signature *)
Structure FunSpec (sig: FunSig) := mkFunSpec {
  pre:  DWORD ^^ sig.(arity) --> SPred;
  post: DWORD ^^ sig.(arity) --> if nonvoid sig then (DWORD * SPred)%type else SPred }.

(* Example spec for an increment function *)
Example incSpec : FunSpec (mkFunSig 1 true)  :=
  @mkFunSpec (mkFunSig 1 true)
    (fun arg => empSP) 
    (fun arg => (incB arg, empSP)). 

(*---------------------------------------------------------------------------
    Helpers
  ---------------------------------------------------------------------------*)
Definition scratchRegisters := [::EAX; ECX; EDX].

Fixpoint scratchedExcept r (rs: seq NonSPReg) : SPred :=
  if rs is r'::rs
  then if r==r' then scratchedExcept r rs
       else r'? ** scratchedExcept r rs
  else empSP.

(*---------------------------------------------------------------------------
    What does it mean to be a function pointer with a particular 
    signature, calling convention and specification?
  ---------------------------------------------------------------------------*)

Definition fastcall_void1_spec (f: DWORD) (FS: FunSpec (mkFunSig 1 false)) : spec :=
  Forall v:DWORD, 
  Forall sp:DWORD, 
  Forall iret:DWORD, 
  (
    safe @ (EIP ~= iret ** ECX?     ** ESP ~= sp    ** sp-#4 :-> ?:DWORD ** post FS v) -->>
    safe @ (EIP ~= f    ** ECX ~= v ** ESP ~= sp-#4 ** sp-#4 :-> iret    ** pre FS  v) 
  ) 
  @ (EAX? ** EDX? ** OSZCP_Any). 

Definition fastcall_nonvoid1_spec (f: DWORD) (FS: FunSpec (mkFunSig 1 true)) : spec :=
  Forall arg:DWORD, 
  Forall sp:DWORD, 
  Forall iret:DWORD, 
  (
    safe @ (EIP ~= iret ** EAX ~= fst (post FS arg) ** ECX?       ** ESP ~= sp    ** sp-#4 :-> ?:DWORD ** snd (post FS arg)) -->>
    safe @ (EIP ~= f    ** EAX?          ** ECX ~= arg ** ESP ~= sp-#4 ** sp-#4 :-> iret    ** pre FS arg) 
  ) 
  @ (EDX? ** OSZCP_Any). 

(* This is a bit gross: we need to say that there is a DWORD extra available on the stack, for saving EBP *)
Definition stdcall_nonvoid1_spec (f: DWORD) (FS: FunSpec (mkFunSig 1 true)) : spec :=
  Forall arg:DWORD, 
  Forall sp:DWORD, 
  Forall iret:DWORD, 
  Forall ebp:DWORD,
  (
    safe @ (EIP ~= iret ** EAX ~= fst (post FS arg) ** ESP ~= sp    ** sp-#4 :-> ?:DWORD ** sp-#8 :-> ?:DWORD ** snd (post FS arg)) -->>
    safe @ (EIP ~= f    ** EAX?          ** ESP ~= sp-#8 ** sp-#4 :-> arg     ** sp-#8 :-> iret    ** pre FS arg) 
  ) 
  @ (EBP ~= ebp ** ECX? ** EDX? ** OSZCP_Any ** sp-#12 :-> ?:DWORD). 

Definition cdecl_nonvoid1_spec (f: DWORD) (FS: FunSpec (mkFunSig 1 true)) : spec :=
  Forall arg:DWORD, 
  Forall sp:DWORD, 
  Forall iret:DWORD, 
  (
    safe @ (EIP ~= iret ** EAX ~= fst (post FS arg) ** ESP ~= sp-#8 ** sp-#4 :-> ?:DWORD ** sp-#8 :-> ?:DWORD ** snd (post FS arg)) -->>
    safe @ (EIP ~= f    ** EAX?          ** ESP ~= sp-#8 ** sp-#4 :-> arg     ** sp-#8 :-> iret    ** pre FS arg) 
  ) 
  @ (ECX? ** EDX? ** OSZCP_Any). 

(*---------------------------------------------------------------------------
    Statement that the body of a nonvoid unary function meets a specification,
    suitable for the fastcall calling convention.
    Note specialization of first argument to ECX.
  ---------------------------------------------------------------------------*)
Definition fastcall_nonvoid1_impMeetsSpec (FS: FunSpec (mkFunSig 1 true)) (FI: programWithSig (mkFunSig 1 true)) : spec :=
  Forall arg:DWORD, 
  basic (EAX?          ** ECX ~= arg ** pre FS arg) (FI ECX)
        (EAX ~= fst (post FS arg) ** ECX? ** snd (post FS arg)) @ (EDX? ** OSZCP_Any).

(*---------------------------------------------------------------------------
    Statement that the body of a nonvoid unary function meets a specification,
    suitable for the cdecl or stdcall calling convention.
    Note specialization of first argument to [EBP+8].  
    Notice that both EBP and the contents of [EBP+8] can be trashed.
  ---------------------------------------------------------------------------*)
Definition stacked_nonvoid1_impMeetsSpec (FS: FunSpec (mkFunSig 1 true)) (FI: programWithSig (mkFunSig 1 true)) : spec :=
  Forall arg:DWORD, Forall ebp:DWORD, 
  basic (EAX?          ** EBP ~= ebp ** ebp +# 8 :-> arg     ** pre FS arg) (FI [EBP+8])
        (EAX ~= fst (post FS arg) ** EBP?       ** ebp +# 8 :-> ?:DWORD ** snd (post FS arg)) @ (ECX? ** EDX? ** OSZCP_Any).

Lemma fastcall_nonvoid1_defCorrect (f f': DWORD) FS FI :
  |-- fastcall_nonvoid1_impMeetsSpec FS FI ->
  |-- fastcall_nonvoid1_spec f FS <@ (f--f' :-> def_fast (mkFunSig 1 true) FI).
Proof.
rewrite /fastcall_nonvoid1_impMeetsSpec/fastcall_nonvoid1_spec/def_fast. 
move => H. 
specintros => arg sp iret.
autorewrite with push_at.
unfold_program. specintros => i'. 

specapply H. sbazooka. 
specapply RET_rule. sbazooka. 
rewrite <-spec_reads_frame. autorewrite with push_at.
rewrite <-spec_later_weaken. apply: limplAdj. apply: landL2. cancel1. sbazooka. 
rewrite subB_equiv_addB_negB. rewrite <-(addBA sp). rewrite (addBC (negB _)). 
rewrite ->(addBA sp).  rewrite addB_negBn. rewrite -(toNatK (zeroExtend _ _)). 
by rewrite toNat_zeroExtend addB0.  
Qed. 

(* Push/pop idiom. It would be nice to have an anti-frame rule so we don't need to mention r in the frame *)
Lemma pushpop_rule (r:NonSPReg) c P Q : 
  |-- basic P c Q ->
  |-- Forall esp:DWORD, Forall v:DWORD, basic P (PUSH r;; c;; POP r) Q @ (r ~= v ** ESP ~= esp ** esp-#4 :-> ?:DWORD).
Proof. 
move => H. 
specintro => esp. specintro => v.
autorewrite with push_at. specintro => old. 
basicapply PUSH_R_rule. 
basicapply H. 
basicapply POP_R_rule.
autorewrite with bitsHints.  
reflexivity. 
Qed.

(* Stack frame idiom *)

Corollary POP_R_ruleAux (r:Reg) (sp:BITS 32) (w:DWORD):
  |-- basic (r? ** ESP ~= sp    ** sp:->w) (POP (RegMemR true r))
            (r ~= w ** ESP ~= sp+#4 ** sp:->w).
Proof. rewrite /regAny. specintros => old. basicapply (POP_rule (RegMemR true r)); sbazooka. Qed. 

Lemma stackframe_rule c P Q ebp esp :
  |-- basic (P ** EBP ~= esp-#4) c (Q ** EBP?) ->
  |-- basic P (PUSH EBP;; MOV EBP, ESP;; c;; POP EBP) Q @ (EBP ~= ebp ** ESP ~= esp ** esp-#4 :-> ?:DWORD).
Proof. 
move => H. 

autorewrite with push_at. specintro => old.
basicapply PUSH_R_rule.
basicapply MOV_RR_rule. rewrite /regAny. sbazooka. 
basicapply H. 
basicapply POP_R_ruleAux. 
autorewrite with bitsHints. reflexivity. 
Qed. 

(* Reorganizing code *)
Lemma stdcall_nonvoid1_defCorrect (f f': DWORD) FS FI :
  |-- stacked_nonvoid1_impMeetsSpec FS FI ->
  |-- stdcall_nonvoid1_spec f FS <@ (f--f' :-> def_std (mkFunSig 1 true) FI).
Proof.
rewrite /stacked_nonvoid1_impMeetsSpec/stdcall_nonvoid1_spec/def_std. 
move => H. 
specintro => arg. specintro => sp. specintro => iret. specintro => ebp. 
autorewrite with push_at.

(* Isolate stackframe idiom *)
rewrite !progEqSeqAssoc.
rewrite <-(progEqSeqAssoc _ _ (introParams 1 8 FI)). 
rewrite <-(progEqSeqAssoc _ _ (POP EBP)). 
rewrite <-(progEqSeqAssoc _ _ (POP EBP)). 
rewrite /introParams.
set C := (PUSH EBP;; _).
unfold_program. specintro => f''.

(* It's rather unpleasant that we have to do this! *)
specapply (@stackframe_rule (FI [EBP+8]) (pre FS arg ** ECX? ** EDX? ** EAX? ** sp-#4 :-> arg ** OSZCP_Any) 
                                          (snd (post FS arg) ** EAX ~= fst (post FS arg) ** ECX? ** EDX? ** OSZCP_Any ** sp-#4 :-> ?:DWORD) ebp (sp-#8)). 

split; last first. rewrite /C. by ssimpl. 
autorewrite with bitsHints. replace (8+4) with 12 by done. by ssimpl.

specapply RET_rule. 
autorewrite with bitsHints. replace (8+4) with 12 by done. by ssimpl. 

rewrite <-spec_reads_frame. autorewrite with push_at.
rewrite <-spec_later_weaken. apply: limplAdj. apply: landL2. cancel1.
 
rewrite -(toNatK (zeroExtend _ _)). rewrite toNat_zeroExtend. rewrite toNat_fromNatBounded => //. 
autorewrite with bitsHints. replace (ESP~=_) with (ESP~=sp) by done.
sbazooka.  
  
specintros => i j. specapply H. ssimpl.
autorewrite with bitsHints. set A := (_ :-> arg). sbazooka. 

rewrite <-spec_reads_frame. autorewrite with push_at.
apply: limplAdj. apply: landL2. cancel1.
ssimpl.  
autorewrite with bitsHints. by set A := (_ :-> ?:DWORD). 
Qed. 


Example incImpCorrect : 
  |-- stacked_nonvoid1_impMeetsSpec incSpec incBody.
Proof.   
rewrite /incSpec/incBody/stacked_nonvoid1_impMeetsSpec/pre/post/fst/snd. 
specintros => arg ebp. 
autorewrite with push_at.
basicapply MOV_RM_rule.
rewrite {1}/OSZCP_Any/OSZCP/flagAny.
specintros => f1 f2 f3 f4 f5.
eapply basic_basic.  apply INC_R_rule. 
rewrite /OSZCP. sbazooka. 
rewrite /OSZCP_Any/OSZCP/flagAny/regAny. 
sbazooka. 
Qed. 

Corollary incImpDefCorrect (f f':DWORD) :
  |-- stdcall_nonvoid1_spec f incSpec <@ (f--f' :-> def_std (mkFunSig 1 true) incBody).
Proof. apply (stdcall_nonvoid1_defCorrect incImpCorrect). Qed.


Definition calleeSpec_fastcall2 (f: DWORD) (P Q: DWORD -> DWORD -> SPred) : spec :=
  Forall v:DWORD,
  Forall w:DWORD, 
  Forall sp:DWORD, 
  Forall iret:DWORD, 
  (
    safe @ (EIP ~= iret ** ECX?     ** EDX?     ** ESP ~= sp    ** sp-#4 :-> ?:DWORD ** Q v w) -->>
    safe @ (EIP ~= f    ** ECX ~= v ** EDX ~= w ** ESP ~= sp-#4 ** sp-#4 :-> iret    ** P v w) 
  ) 
  @ EAX?.

(*
Lemma spec_at_calleeSpec_fastcall1 f P Q R:
  calleeSpec_fastcall1 f P Q @ R -|- calleeSpec_fastcall1 f (fun v => P v ** R) (fun v => Q v ** R).
Proof.
  rewrite /calleeSpec_fastcall1. 
  autorewrite with push_at. cancel1 => v.
  autorewrite with push_at. cancel1 => esp. 
  autorewrite with push_at. cancel1 => w. 
  autorewrite with push_at.
  (* This is tedious. What tactic should we use? *)
  rewrite !sepSPA. 
  rewrite (sepSPC R). 
  rewrite !sepSPA. 
  reflexivity. 
Qed.
Hint Rewrite spec_at_calleeSpec_fastcall1 : push_at.


Require Import cursor.

Lemma fastcall1_callEAX f P Q:
  |> calleeSpec_fastcall1 f P Q |--
     Forall v:DWORD, 
     Forall esp:DWORD,
     basic (EAX ~= v ** P v) (call_fast_with 1 f EAX) (EAX? ** Q v) @ 
         (EDX? ** ECX? ** ESP ~= esp ** esp-#4 :-> ?:DWORD) (* trash EAX, ECX, EDX and top of stack *). 
Proof. 
specintro => v. 
specintro => esp.  
autorewrite with push_at. 
specintro => old. 
rewrite /call_fast_with/pushFastArgs/makeMOVsrc. 

(* MOV *)
eapply basic_seq. basicapply MOV_RR_rule. 

(* CALL *)
rewrite /basic. specintros => i j. unfold_program. rewrite /calleeSpec_fastcall1.
specapply (CALL_I_rule (addr:=f)). sbazooka.
rewrite <-spec_reads_frame.
autorewrite with push_at. 
rewrite spec_later_forall. eapply lforallL.  
rewrite spec_later_forall. eapply lforallL.  
rewrite spec_later_forall. eapply lforallL.  
autorewrite with push_at.
rewrite ->spec_later_impl.  
rewrite <-spec_later_weaken.

rewrite /regAny. eapply SAFEY; sbazooka. 
Qed. 

Definition scratch := EAX? ** ECX? ** EDX? ** OSZCP_Any.

Definition calleeSpec_stdcall1 (f: DWORD) (P Q: DWORD -> SPred) : spec :=
  Forall v:DWORD, 
  Forall sp:DWORD, 
  Forall iret:DWORD, 
  (
    safe @ (EIP ~= iret ** ESP ~= sp ** sp-#4 :-> ?:DWORD ** sp-#8 :-> ?:DWORD ** Q v) -->>
    safe @ (EIP ~= f    ** ESP ~= sp-#8 ** sp-#4 :-> v ** sp-#8 :-> iret ** P v) 
  ) 
  @ scratch.



Lemma SILLY P Q :
  P ** Q |-- (P ** ltrue) //\\ (P ** Q). 
Proof.
rewrite sepSPC. rewrite (sepSPC P). 
rewrite <- land_sepSP. sbazooka. apply landR => //. 
Qed. 

Fixpoint regIsIn (r: NonSPReg) (rs: seq NonSPReg) :=
  if rs is r'::rs then 
  (r == r') || regIsIn r rs else false. 

Lemma stdcall1_call f P Q (r: NonSPReg):
  |> calleeSpec_stdcall1 f P Q |--
     Forall v: DWORD, Forall esp: DWORD,
     basic (r ~= v ** scratchedExcept r scratchRegisters ** OSZCP_Any ** P v)
           (call_std_with 1 f v) 
           ((if regIsIn r scratchRegisters then r? else r ~= v) ** scratchedExcept r scratchRegisters ** OSZCP_Any ** Q v) @ 
           (ESP ~= esp ** esp-#4 :-> ?:DWORD ** esp-#8 :-> ?:DWORD).

Proof.
specintro => v. specintro => esp.  
autorewrite with push_at. 
specintros => old1 old2. rewrite /call_std_with/pushArgs.

(* PUSH *)
eapply basic_seq. basicapply PUSH_I_rule. 

(* CALL *)
rewrite /basic. specintros => i j. unfold_program. 
specapply (CALL_I_rule (addr:=f)). sbazooka. rewrite -subB_addn. replace (4+4) with 8 by done. sbazooka.
rewrite <-spec_reads_frame.
autorewrite with push_at. 
rewrite spec_later_forall. apply lforallL with v.  
rewrite spec_later_forall. apply lforallL with esp.  
rewrite spec_later_forall. apply lforallL with j.  
autorewrite with push_at.
rewrite ->spec_later_impl.  
rewrite <-spec_later_weaken.
autorewrite with push_at. rewrite /scratch.
case: r.
(* EAX  *)
eapply SAFEY; simpl (regIsIn _ _); simpl (scratchedExcept _ _); rewrite /regAny; ssimpl => //. 
rewrite -subB_addn. replace (4+4) with 8 by done. sbazooka.  
(* EBX *)
rewrite -> (spec_frame (EBX~=v)). autorewrite with push_at. 
eapply SAFEY; simpl (regIsIn _ _); simpl (scratchedExcept _ _). sbazooka. 
ssimpl. rewrite -subB_addn. replace (4+4) with 8 by done. sbazooka. 
(* ECX *)
eapply SAFEY; simpl (regIsIn _ _); simpl (scratchedExcept _ _); rewrite /regAny; ssimpl => //. 
rewrite -subB_addn. replace (4+4) with 8 by done. sbazooka.  
(* EDX *)
eapply SAFEY; simpl (regIsIn _ _); simpl (scratchedExcept _ _); rewrite /regAny; ssimpl => //. 
rewrite -subB_addn. replace (4+4) with 8 by done. sbazooka.  
(* ESI *)
rewrite -> (spec_frame (ESI~=v)). autorewrite with push_at. 
eapply SAFEY; simpl (regIsIn _ _); simpl (scratchedExcept _ _). sbazooka. 
ssimpl. rewrite -subB_addn. replace (4+4) with 8 by done. sbazooka. 
(* EDI *)
rewrite -> (spec_frame (EDI~=v)). autorewrite with push_at. 
eapply SAFEY; simpl (regIsIn _ _); simpl (scratchedExcept _ _). sbazooka. 
ssimpl. rewrite -subB_addn. replace (4+4) with 8 by done. sbazooka. 
(* EBP *)
rewrite -> (spec_frame (EBP~=v)). autorewrite with push_at. 
eapply SAFEY; simpl (regIsIn _ _); simpl (scratchedExcept _ _). sbazooka. 
ssimpl. rewrite -subB_addn. replace (4+4) with 8 by done. sbazooka. 
Qed. 

Example stdcall1_example_callee : program :=
  def_std 1 (fun arg => 
    makeBOP OP_ADD arg arg;;
    INC arg;;
    MOV EAX, arg
  )%asm.

Lemma fastcall2_call f P Q v w esp:
  |> calleeSpec_fastcall2 f P Q |--
     basic (P v w) (call_fast_with 2 f v w) (Q v w) @ 
         (EAX? ** EDX? ** ECX? ** ESP ~= esp ** esp-#4 :-> ?:DWORD) (* trash EAX, ECX, EDX and top of stack *). 
Proof. 
autorewrite with push_at. 
specintros => old. rewrite /call_fast_with/pushFastArgs/makeMOVsrc. 

(* MOV *)
eapply basic_seq. basicapply MOV_RI_rule. 
eapply basic_seq. basicapply MOV_RI_rule. 

(* CALL *)
rewrite /basic. specintros => i j. unfold_program. rewrite /calleeSpec_fastcall2.
specapply (CALL_I_rule (addr:=f)). sbazooka.
rewrite <-spec_reads_frame.
autorewrite with push_at. 
rewrite spec_later_forall. eapply lforallL.  
rewrite spec_later_forall. eapply lforallL.  
rewrite spec_later_forall. eapply lforallL.  
rewrite spec_later_forall. eapply lforallL.  
autorewrite with push_at.
rewrite ->spec_later_impl.  
rewrite <-spec_later_weaken.

eapply SAFEY; sbazooka. 
Qed. *)