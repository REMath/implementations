Require Import ssreflect ssrbool ssrnat eqtype seq fintype.
Require Import procstate procstatemonad bitsops bitsprops bitsopsprops.
Require Import SPred septac spec spectac safe basic program.
Require Import instr instrsyntax decinstr instrrules reader pointsto cursor.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope instr_scope.
(* Allocation invariant: 
     infoBlock points to a pair of DWORDs:
       base, a pointer to the current available heap
       count, the number of bytes currently available
   Furthermore, "count" bytes of memory starting at "base" is defined
*)
Definition allocInv (infoBlock: DWORD) :=
  Exists base: DWORD, 
  Exists count: DWORD,
  infoBlock :-> base **
  infoBlock +#4 :-> count **
  memAny base count.

(* Allocate memory.
     infoBlock: Src  is pointer to two-word heap information block
     n: nat representing number of bytes to be allocated
     failed: DWORD is label to branch to on failure
   If successful, EDI contains pointer to byte just beyond allocated block. 
*)
Definition allocImp infoBlock (n: nat) (failed: DWORD) : program :=
  MOV ESI, infoBlock;;
  MOV EDI, [ESI];;
  ADD EDI, n;;
  JC  failed;;  (* A carry indicates unsigned overflow *)
  CMP [ESI+4], EDI;;
  JC  failed;;  (* A carry indicates unsigned underflow *)
  MOV [ESI], EDI.

Definition allocSpec n fail inv code :=
  Forall i, Forall j, (
      safe @ (EIP ~= fail ** EDI?) //\\
      safe @ (EIP ~= j ** Exists p, EDI ~= p +# n ** memAny p (p +# n))
    -->>
      safe @ (EIP ~= i ** EDI?)
    )
    @ (ESI? ** OSZCP_Any ** inv)
    <@ (i -- j :-> code).

Hint Unfold allocSpec : specapply.

(* Perhaps put a |> on the failLabel case *)

Lemma inlineAlloc_correct n failed infoBlock : |-- allocSpec n failed (allocInv infoBlock) (allocImp infoBlock n failed).  
Proof.  
  rewrite /allocImp/allocSpec. specintros => i j. unfold_program.
  specintros => i1 i2 i3 i4 i5 i6.

  (* MOV ESI, infoBlock *)
  specapply MOV_RI_rule.
  by ssimpl.

  (* MOV EDI, [ESI] *)
  rewrite {2}/allocInv. specintros => base limit.
  specapply MOV_RM0_rule.
  by ssimpl.

  (* ADD EDI, bytes *)
  elim E:(splitmsb (adcB false base (fromNat n))) => [carry res].
  rewrite /ConstImm. specapply ADD_RI_rule.
  by ssimpl.

  (* JC failed *)
  rewrite E. specapply JC_rule.
  rewrite /OSZCP. ssimpl. by ssimpl.

  specsplit.
    rewrite <-spec_reads_frame. rewrite <-spec_later_weaken.
    autorewrite with push_at. apply limplValid. apply landL1. cancel1.
    rewrite /OSZCP_Any /flagAny /regAny /allocInv. by sbazooka.

  (* CMP [ESI+4], EDI *)
  specintro. move/eqP => Hcarry. subst carry.
  elim E0:(sbbB false limit res) => [carry0 res0].
  specapply CMP_MR_rule; last eassumption.
  - rewrite /OSZCP_Any /flagAny. by sbazooka.

  (* JC failed *)
  specapply JC_rule.
  - rewrite /OSZCP. by ssimpl.

  specsplit.
  - rewrite <-spec_reads_frame. rewrite <-spec_later_weaken.
    autorewrite with push_at. apply limplValid. apply landL1. cancel1.
    rewrite /OSZCP_Any /flagAny /regAny /allocInv. by sbazooka.

  (* MOV [ESI], EDI *)
  specintro. move/eqP => Hcarry0. subst carry0.
  specapply MOV_M0R_rule.
  - by ssimpl.
  rewrite <-spec_reads_frame. apply limplValid. autorewrite with push_at.
  apply: landL2. cancel1.
  rewrite /OSZCP_Any /flagAny /regAny /allocInv. ssplits.

  ssimpl.
  have Hres: base +# n = res by rewrite /addB /dropmsb E.
  have Hless1 := addB_leB E.
  have Hless2 := sbbB_ltB_leB limit res. rewrite E0 /= in Hless2.
  rewrite <-Hres in *.
  ssimpl. by apply memAnySplit.
Qed.



