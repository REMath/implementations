Require Import ssreflect ssrbool ssrnat eqtype seq fintype.
Require Import procstate procstatemonad bitsops bitsprops bitsopsprops.
Require Import SPred septac spec spectac safe basic program.
Require Import instr instrsyntax decinstr instrrules reader pointsto cursor.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope instr_scope.

(* Allocation invariant: 
     info points to a pair of DWORDs:
       base, a pointer to the current available heap
       count, the number of bytes currently available
   Furthermore, "count" bytes of memory starting at "base" is defined
*)
Definition allocInv (info: DWORD) :=
  Exists base: DWORD, 
  Exists count: DWORD,
  info :-> base **
  info +#4 :-> count **
  memAny base count.

(* Allocate memory.
     info: Src  is pointer to two-word heap information block
     n: nat representing number of bytes to be allocated
     fail: DWORD is label to branch to on failure
   If successful, EDI contains pointer to byte just beyond allocated block. 
*)
Definition allocImp info (n: nat) (fail: DWORD) : program :=
  mov ESI, info;;
  mov EDI, [ESI];;
  add EDI, n;;
  jc fail;;  (* A carry indicates unsigned overflow *)
  cmp [ESI+4], EDI;;
  jc fail;;  (* A carry indicates unsigned underflow *)
  mov [ESI], EDI.

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
Lemma inlineAlloc_correct n fail info : |-- allocSpec n fail (allocInv info) (allocImp info n fail).  
Proof.  
  rewrite /allocImp/allocSpec /memIs /programMemIs. 
  specintros => i j i1 i2 i3 i4 i5 i6.

  (* mov ESI, heapInfo *)
  specapply MOV_RI_rule.
  - by ssimpl.

  (* mov EDI, [ESI] *)
  rewrite {2}/allocInv. specintros => base limit.
  specapply MOV_RM0_rule.
  - by ssimpl.

  (* add EDI, bytes *)
  elim E:(splitmsb (adcB false base (fromNat n))) => [carry res].
  specapply ADD_RI_rule; last eassumption.
  - by ssimpl.

  (* jc failLabel *)
  specapply JC_rule.
  - rewrite /OSZCP. by ssimpl.

  specsplit.
  - rewrite <-spec_reads_frame. rewrite <-spec_later_weaken.
    autorewrite with push_at. apply limplValid. apply landL1. cancel1.
    rewrite /OSZCP_Any /flagAny /regAny /allocInv. by sbazooka.

  (* cmp [ESI+4], EDI *)
  specintro. move/eqP => Hcarry. subst carry.
  elim E0:(sbbB false limit res) => [carry0 res0].
  specapply CMP_MR_rule; last eassumption.
  - rewrite /OSZCP_Any /flagAny. by sbazooka.

  (* jc failLabel *)
  specapply JC_rule.
  - rewrite /OSZCP. by ssimpl.

  specsplit.
  - rewrite <-spec_reads_frame. rewrite <-spec_later_weaken.
    autorewrite with push_at. apply limplValid. apply landL1. cancel1.
    rewrite /OSZCP_Any /flagAny /regAny /allocInv. by sbazooka.

  (* mov [ESI], EDI *)
  specintro. move/eqP => Hcarry0. subst carry0.
  specapply MOV_M0R_rule.
  - by ssimpl.
  rewrite <-spec_reads_frame. apply limplValid. autorewrite with push_at.
  apply: landL2. cancel1.
  rewrite /OSZCP_Any /flagAny /regAny /allocInv. sbazooka.

  (* Arithmetic epilogue *)
  have Hres: base +# n = res by rewrite /addB /dropmsb E.
  have Hless1 := addB_leB E.
  have Hless2 := sbbB_ltB_leB limit res. rewrite E0 /= in Hless2.
  rewrite <-Hres in *. ssimpl. by apply memAnySplit.
Qed.

