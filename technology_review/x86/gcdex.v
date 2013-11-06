Require Import ssreflect ssrbool ssrnat eqtype seq finfun tuple fintype.
Require Import bitsrep ilogic.
Require Import program programassem assemproof imp.
Require Import reader SPred septac pointsto spec spectac basic reg.
Require Import cursor safe instrrules.
Require Import instr instrsyntax macros Ascii bitsops bitsprops bitsopsprops.
Require Import screenspec screenimp.

Open Scope instr_scope.
Local Transparent ILFun_Ops.

Definition codeAddr:DWORD := #x"300000".

Definition Cgcd :=
  Cseq (Cassign xa (eliteral #100)) (
  Cseq (Cassign xb (eliteral #60)) ( (* their GCD is 20, which is octal 024 *)
  Cwhile (esubtract xa xb) (
    Cif (elessthan xa xb) (
      Cassign xb (esubtract xb xa)
    ) (
      Cassign xa (esubtract xa xb)
    )
  )
  )).

(* TODO: stronger spec *)
Lemma Cgcd_correct:
  |-- triple ltrue Cgcd ltrue.
Proof.
  eapply triple_seq.
  - eapply triple_roc; [|done|apply triple_assign].
    apply subst_true_special_case.
  eapply triple_seq.
  - eapply triple_roc; [|done|apply triple_assign].
    apply subst_true_special_case.
  eapply triple_roc; last apply triple_while.
  - reflexivity.
  - done.
  eapply triple_roc; last apply triple_if.
  - reflexivity.
  - reflexivity.
  - eapply triple_roc; last apply triple_assign; last reflexivity.
    move=> s H. apply I.
  - eapply triple_roc; last apply triple_assign; last reflexivity.
    move=> s H. apply I.
Qed.

Definition gcd_program : program := compile_cmd Cgcd.

Definition gcd_bytes : seq BYTE := assemble_total codeAddr gcd_program.

Definition screenAddr: DWORD := screenBase +# numCols*2*32.
Definition rightpos: DWORD := screenAddr +# (2*(11-1)).
Definition showOctal_program : program :=
    (* A 32-bit octal number can take up 11 digits. Each digit is two bytes. *)
      (* Print EAX in octal, stepping on EBX and EDX *)
      mov EBX, rightpos;;
      mov ECX, 3;;
      while (test EAX, EAX) CC_Z false ( (* while EAX <> 0 *)
        mov EDX, 7;; (* bit mask *)
        and EDX, EAX;;
        add EDX, (nat_of_ascii "0");;
        mov byte [EBX], EDX;; (* write to screen *)
        shr EAX, 3;; (* shift right *)
        sub EBX, 2(* move one character left on the screen *)
      ).

Theorem gcd_safe: forall endAddr: DWORD,
  |-- (safe @ (EIP ~= endAddr) -->> safe @ (EIP ~= codeAddr))
        @ (EAX? ** EBX? ** ECX? ** EDX? ** OSZCP_Any)
       <@ (codeAddr -- endAddr :-> gcd_bytes).
Proof.
  move=> endAddr. rewrite /gcd_bytes.
  rewrite ->assem_total_correct; last by vm_compute.
  rewrite /gcd_program.
  have H := Cgcd_correct. rewrite /triple in H. autorewrite with push_at in H.
  specapply H.
  - ssimpl. rewrite /asn_denot /stack_denot. rewrite /regAny.
    sdestructs => a b c.
    pose s x := match x with | xa => a | xb => b | xc => c end.
    ssplit. instantiate (2:=s). by sbazooka.
  rewrite <-spec_reads_frame. apply limplValid. autorewrite with push_at.
  cancel1. rewrite /asn_denot /stack_denot /regAny. by sbazooka.
Qed.

(* This is the plain version of the theorem, not obscured by fancy spec logic
   constructs. *)
Corollary gcd_safe_nonfancy: forall (endAddr: DWORD) k R,
  safe k (EIP ~= endAddr ** EAX? ** EBX? ** ECX? ** EDX? ** OSZCP_Any **
          codeAddr -- endAddr :-> gcd_bytes ** R) ->
  safe k (EIP ~= codeAddr ** EAX? ** EBX? ** ECX? ** EDX? ** OSZCP_Any **
          codeAddr -- endAddr :-> gcd_bytes ** R).
Proof.
  move=> endAddr k R.
  pose proof (gcd_safe endAddr). rewrite ->spec_reads_entails_at in H; [|apply _].
  autorewrite with push_at in H.
  apply landAdj in H. lforwardL H.
  - apply landR; [apply ltrueR|done].
  specialize (H k R). simpl in H. rewrite ->!sepSPA in H. apply H.
Qed.

Definition gcdEx : seq BYTE :=
  assemble_total codeAddr (
  gcd_program;;
    clsProg;;
    showOctal_program;;
    LOCAL busy;
      busy:;;
        jmp busy
  ).

