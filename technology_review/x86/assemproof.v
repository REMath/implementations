Require Import ssreflect ssrnat ssrbool seq eqtype tuple.
Require Import tuplehelp bitsrep bitsprops bitsops bitsopsprops instr encinstr decinstr.
Require Import roundtrip.
Require Import program programassem monad monadinst.
Require Import reader SPred septac pointsto cursor.

Require sparsefun. (* Everything in here has very short names. *)
Module SF := sparsefun.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* TODO: change readerMemIs so it won't be necessary to do this *)
Transparent ILFun_Ops.

Lemma Instr_codec_pointsto (p q: DWORD) (c: Instr):
  p -- q :-> encodeInstr p c |-- p -- q :-> c.
Proof.
  rewrite ->seqMemIs_reader.
  move=> s [m [Hok Hrange]]. exists m.
  split; last done. apply roundtripInstr. apply Hok.
Qed.

Opaque ILFun_Ops.

Lemma sepSPltrue P: P |-- P ** ltrue.
Proof. etransitivity; [apply empSPR|]. cancel2. Qed.

Lemma pass2_correct addrs p labelno labelno' pos pos' code code':
  pass2 addrs p (pos, labelno, code) = Some ((pos', labelno', code'), tt) ->
  exists newcode, code' = code ++ newcode /\ pos' = pos +# size newcode /\
  pos -- pos' :-> newcode |-- pos -- pos' :-> p ** ltrue.
Proof.
  move: labelno labelno' pos pos' code code'.
  induction p => labelno labelno' pos pos' code code'.
  - rewrite /pass2 SMT_bindGet.
    case Hsplit: (splitmsb (adcB false pos #(size (encodeInstr pos c))))
      => [carry res].
    destruct carry; first done.
    rewrite /setState2 /SMT_set /retn /optionMonadOps.
    move=> [Hpos'] _ [Hcode']. subst res code'.
    eexists. split; [reflexivity|]. split.
    - rewrite /addB /dropmsb Hsplit. done.
    rewrite <-sepSPltrue. exact: Instr_codec_pointsto.
  - rewrite /pass2. move=> [->] _ [->]. exists nil.
    split; first by rewrite cats0.
    split; first by rewrite addB0.
    rewrite /memIs /seqMemIs /programMemIs. by sbazooka.
  - rewrite /pass2 -/pass2.
    rewrite /bind /SMT_ops /optionMonadOps /bind.
    case Hp1: (pass2 addrs p1 (pos, labelno, code))
      => // [[[[pos1 labelno1] code1] []]].
    edestruct IHp1 as [newcode1 [Hcode1 [Hpos1 Hentails1]]]; [apply Hp1|].
    move=> Hp2.
    edestruct IHp2 as [newcode2 [Hcode' [Hpos' Hentails2]]]; [apply Hp2|].
    move=> {IHp1 IHp2}.
    subst pos1 pos'. rewrite <-addB_addn, <-size_cat in *.
    exists (newcode1 ++ newcode2). split.
    - rewrite Hcode' Hcode1. by rewrite catA.
    split; first done.
    rewrite ->seqMemIs_cat. apply: lexistsL => pos'. rewrite /fst /snd.
    case: pos' => [pos'|]; last first.
    - rewrite ->seq_BYTE_hwm. rewrite lfalse_is_exists. by sdestruct => [[]].
    rewrite ->seq_BYTE_size. sdestruct => Hpos'. subst pos'.
    rewrite ->Hentails1. rewrite ->Hentails2.
    rewrite {3}/memIs /programMemIs -/programMemIs. ssplit.
    by ssimpl.
  - rewrite /pass2 -/pass2 SMT_bindGet.
    rewrite {1}/bind /SMT_ops /SMT_lift assoc.
    rewrite {1}/bind /optionMonadOps.
    case _: (SF.get addrs labelno) => // [addr].
    rewrite id_l SMT_doSet => Hrec.
    edestruct H as [newcode [Hcode' [Hpos' Hentails]]]; [apply Hrec|].
    eexists. split; [apply Hcode'|]. split; first done.
    rewrite ->Hentails. cancel2.
    apply lexistsR with addr; rewrite -/programMemIs. reflexivity.
  - rewrite /pass2 SMT_bindGet.
    case Hl: (pos == l) => //.
    move/eqP: Hl => <-.
    move=> [Hpos] _ [Hcode]. subst pos' code'.
    exists nil.
    split; first by rewrite cats0.
    split; first by rewrite addB0.
    rewrite /memIs /seqMemIs /programMemIs. by sbazooka.
Qed.

(* The annoying [ltrue] in the conclusion here comes from the fact that
   points-to for [seq BYTE] is a readerMemIs, which is closed under heap
   extension. We need to make that strictly exact.
 *)

Theorem assem_correct (offset endpos: DWORD) p code:
  assemble_program offset p = Some code ->
  offset -- endpos :-> code |-- offset -- endpos :-> p ** ltrue.
Proof.
  rewrite /assemble_program.
  set addrs := do_pass1 offset p.
  rewrite /do_pass2. 
  case Hpass2: (pass2 addrs p (offset, 0, [::])) =>
    [[[[pos' labelno'] code'] []]|]; last done.
  move=> [<-] {code}.
  apply pass2_correct in Hpass2.
  case: Hpass2 => newcode [Hcode' [Hpos' Hentails]].
  rewrite /= in Hcode'. subst code' pos'.
  rewrite ->seq_BYTE_size. by sdestruct => ->.
Qed.

(* Discharge the side condition with [by vm_compute]. *)
Theorem assem_total_correct (offset endpos: DWORD) p:
  assemble_success offset p = true ->
  offset -- endpos :-> assemble_total offset p |--
    offset -- endpos :-> p ** ltrue.
Proof.
  rewrite /assemble_success /assemble_total.
  case Hasm: (assemble_program offset p) => [code|]; last done.
  move=> _. exact: assem_correct.
Qed.
  
