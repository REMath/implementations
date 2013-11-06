(*===========================================================================
  Wrapped allocator
  ===========================================================================*)
Require Import ssreflect ssrbool ssrnat eqtype seq fintype tuple.
Require Import procstate procstatemonad bitsrep bitsops bitsprops bitsopsprops.
Require Import SPred septac spec spectac safe basic program.
Require Import call instr instrsyntax decinstr instrrules reader pointsto cursor inlinealloc 
               listspec listimp triple macros.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition wrappedAlloc bytes (r1 r2:Reg) heapInfo: program :=
  (LOCAL FAIL;
  LOCAL SUCCEED;
    allocImp heapInfo bytes FAIL;;
    SUB EDI, bytes;;
    JMP SUCCEED;;
  FAIL:;;
    MOV EDI, 0;;
  SUCCEED:;)
  %asm.

Lemma wrappedAlloc_correct bytes (r1 r2: Reg) heapInfo : 
  |-- Forall i: DWORD, Forall j: DWORD,   
  toyfun i EDI? ((Exists p, EDI ~= p ** memAny p (p +# bytes)) \\// EDI ~= #0) 

  @  (ESI? ** OSZCP_Any ** allocInv heapInfo) 
  <@ (i -- j :-> mkbody_toyfun (wrappedAlloc bytes r1 r2 heapInfo)). 
Proof. 
specintros => i j. 

(* First deal with the calling-convention wrapper *)
autorewrite with push_at.  
etransitivity; [|apply toyfun_mkbody]. specintro => iret.

(* Now unfold the control-flow logic *)
rewrite /wrappedAlloc/basic. specintros => i1 i2. unfold_program. 
specintros => i3 i4 i5 i6 i7 i8 -> -> i9 -> ->.

(* Deal with the allocator spec itself *)  
specapply inlineAlloc_correct.  
- by ssimpl. 

(* Now we deal with failure and success cases *)
specsplit. 

(* failure case *)
autorewrite with push_at.

(* MOV EDI, 0 *)
rewrite /ConstImm.
specapply MOV_RI_rule. 
- by ssimpl.
rewrite <- spec_reads_frame. apply: limplAdj. apply: landL2. 
autorewrite with push_at. cancel1. ssimpl. by apply: lorR2. 

(* success case *)
autorewrite with push_at. 

(* SUB EDI, bytes *)
specintros => pb. 

(* Subtraction arithmetic *)
elim E0:(sbbB false (pb+#bytes) (# bytes)) => [carry0 res0].      
assert (H:= subB_equiv_addB_negB (pb+#bytes) # bytes). rewrite /subB in H. 
rewrite E0 in H. simpl (snd _) in H. rewrite addB_negBn in H.
rewrite H in E0.

rewrite /ConstImm.
specapply SUB_RI_rule; last eassumption.
- by ssimpl.

(* JMP SUCCEED *)
specapply JMP_I_rule.
- by ssimpl. 

(* Final stuff *)
rewrite <-spec_later_weaken.
rewrite <-spec_reads_frame. 
apply: limplAdj. autorewrite with push_at. 
apply: landL2. cancel1. 
rewrite /OSZCP/OSZCP_Any/flagAny/regAny. sbazooka. apply: lorR1.
 
sbazooka. 
Qed. 
