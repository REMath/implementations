(*===========================================================================
    Assembler for type [program]. Import this and call [assemble_program].
  ===========================================================================*)
Require Import ssreflect ssrnat ssrbool seq eqtype tuple.
Require Import tuplehelp bitsrep bitsops mem reg instr instrsyntax encinstr cursor update.
Require Import program monad monadinst writer.
Require Import SPred septac pointsto reader decinstr roundtrip roundtripinstr.

Require sparsefun. (* Everything in here has very short names. *)
Module SF := sparsefun.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Here's how it works.

   The first pass serves only to guess label addresses, producing a map from
   label positions (counted left to right, top to bottom in the program) to
   memory offsets. It does not come with a correctness proof, so it might be
   wrong; indeed, it will be wrong if the program does forbidden things such as
   using the same label twice or inspecting label addresses.

   The second pass uses the generated map to fill in an address every time it
   encounters a [prog_declabel]. When it later encounters [prog_label l], it
   checks that [l] corresponds to the current address. If this check fails, the
   whole assembly process fails.

   First pass in detail:
   - We thread through a current position and the label map in a state monad.
   - When we meet a declabel, we allocate a new position in the label map and
     pass the identifier for this position in as the label value.
     - This abuses the fact that labels are of type DWORD, which is for all
       practical purposes a large enough type to inject label numbers (of type
       nat) into. It's a poor man's version of Chlipala's PHOAS.
   - When we meet label l, remember that (l: DWORD) is actually a label
     identifier rather than an address. We imperatively update the label map so
     it maps label l to the current position.
   - When we meet an instruction, add its size to the current position.
 *)

Definition labelmap := SF.SFun DWORD.

(* Current position in memory , map from label number to label position *)
Definition state1 := (DWORD * labelmap)%type.

Definition dummyValue := #x"EFBEADDE". 

(* BEWARE: I assume that SF.alloc will allocate addresses in sequential
   order. *)
Fixpoint pass1 (p: program) : @SM state1 unit :=
  match p with
  | prog_instr c =>
      let! (pos, addrs) = SM_get;
      if
        let! (_, bytes) = runWriterTm (writeNext c) (mkCursor pos);
        nexts (size bytes) pos
      is (Some (mkCursor pos')) then SM_set (pos', addrs) else retn tt
  | prog_data _ _ _ _ c =>
      let! (pos, addrs) = SM_get;
      if
        let! (_, bytes) = runWriterTm (writeNext c) (mkCursor pos);
        nexts (size bytes) pos
      is (Some (mkCursor pos')) then SM_set (pos', addrs) else retn tt
  | prog_skip => retn tt
  | prog_seq p1 p2 =>
      do!  pass1 p1;
           pass1 p2
  | prog_declabel _ body =>
      let! (pos, addrs) = SM_get;
      let: (addrs, labelno) := SF.alloc addrs dummyValue in
      do!  SM_set (pos, addrs);
           pass1 (body (dummyValue +#labelno)) 
  | prog_label l =>
      let! (pos, addrs) = SM_get;
      let  addrs := SF.put addrs (toNat (subB l dummyValue)) pos in
           SM_set (pos, addrs)
  end.

Definition do_pass1 (offset: DWORD) (p: program) : labelmap :=
  let: ((_, addrs), _) := pass1 p (offset, SF.empty) in
  addrs.

(* Current label number *)
Definition state2 := nat.

(* The monad in which pass 2 does its computation. This unfolds to
   fun X => state2 -> WriterTm (state2 * X) *)
Definition ST2 := @SMT WriterTm state2.

Definition getState2: ST2 state2 := SMT_get _ (S:=_).
Definition setState2: state2 -> ST2 unit := SMT_set _ (S:=_). 
Definition lift2 {X} (w: WriterTm X): ST2 X := SMT_lift _ w.

Fixpoint pass2 (addrs: labelmap) (p: program) : ST2 unit :=
  match p with
  | prog_instr c => lift2 (writeNext c)
  | prog_data _ _ _ _ c => lift2 (writeNext c)
  | prog_skip => retn tt
  | prog_seq p1 p2 =>
      do! pass2 addrs p1;
          pass2 addrs p2
  | prog_declabel _ body =>
      let! labelno = getState2;
      match SF.get addrs labelno with
      | None => lift2 writerFail
      | Some addr =>
          do! setState2 labelno.+1;
              pass2 addrs (body addr)
      end
  | prog_label l =>
      let! pos = lift2 getWCursor;
      if pos == l then retn tt else lift2 writerFail
  end.

Instance write_program : Writer program :=
  fun p =>
    let! c = getWCursor;
    if c is mkCursor offset
    then
      let addrs := do_pass1 offset p in
      do! pass2 addrs p 0;
          retn tt
    else writerFail.

(* This is the main function of the assembler. *)
Definition assemble (offset: DWORD) (p: program) : seq BYTE :=
  match runWriter write_program offset p with
  | Some code => code
  | None => nil
  end.

(* Call this to determine whether the assembler returned something meaningful.
 *)
Definition assemble_success (offset: DWORD) (p: program) : bool :=
  match runWriter write_program offset p with
  | Some code => true
  | None => false
  end.


Lemma pass2_correct addrs p labelno (pos pos': DWORD) arg:
  interpWriterTm (pass2 addrs p labelno) pos pos' arg |-- pos -- pos' :-> p.
Proof.
  move: labelno pos pos' arg.
  induction p => labelno pos pos' arg.

  (* prog_instr *)
    simpl. rewrite /lift2 /SMT_lift.
    apply interpWriterTm_roundtrip.
    rewrite -(id_r _ readInstr). rewrite doLet.
    apply: simrw_bind. constructor.
  (* prog_skip *)
    simpl. sdestructs => [_ [<-]]. rewrite /memIs /interpProgram.
    case: pos; intros; by ssplit.
  (* prog_seq *)
    rewrite /pass2 -/pass2.
    rewrite interpWriterTm_bind. sdestructs => p' [st []].
    rewrite /memIs /interpProgram.
    case: p' => [p'|]; last first.
    - rewrite ->interpWriterTm_hwm. by ssimpl.
    ssplit. by cancel2.
  (* prog_declabel *)
    rewrite /pass2 -/pass2 SMT_bindGet.
    case _: (SF.get addrs labelno) => [addr|]; last exact: lfalseL.
    rewrite SMT_doSet. rewrite /memIs/interpProgram-/interpProgram.
    ssplit. by apply H.
  (* prog_label *)
    simpl.
    case Hl: (mkCursor pos == mkCursor l); last exact: lfalseL.
    move/eqP: Hl => [<-].
    rewrite /memIs /seqMemIs /interpProgram /=.
    by sbazooka; congruence.

  (* prog_data *)
    rewrite /pass2. rewrite /lift2 /SMT_lift.
    apply interpWriterTm_roundtrip.
    rewrite <-(id_r _ _). rewrite doLet.
    apply: simrw_bind. constructor.

Qed.

(*=write_program_correct *)
Theorem write_program_correct (i j: DWORD) (p: program):
  interpWriter i j p |-- i -- j :-> p.
(*=End *)
Proof.
  rewrite /interpWriter /=.
  rewrite interpWriterTm_bind. sdestructs => j' [labelno []].
  rewrite {2}/interpWriterTm. sdestructs => _ ->. ssimpl.
  exact: pass2_correct.
Qed.

(* When applying this lemma, discharge the side condition with [by vm_compute].
 *)
Theorem assemble_correct (offset endpos: DWORD) p:
  assemble_success offset p = true ->
  offset -- endpos :-> assemble offset p |-- offset -- endpos :-> p.
Proof.
  rewrite /assemble_success /assemble.
  case Hcode: (runWriter write_program offset p) => [code|]; last done.
  move=> _. rewrite ->runWriter_interpWriter; last eassumption.
  exact: write_program_correct.
Qed.


(* Current label number, current result *)
Definition exportList := list (string * DWORD).
Definition state3 := (nat * exportList)%type.

(* The monad in which the export pass does its computation. *)
Definition ST3 := @SMT option state3.

Definition getState3: ST3 state3 := SMT_get _ (S:=_).
Definition setState3: state3 -> ST3 unit := SMT_set _ (S:=_).
Definition lift3 {X} (o: option X): ST3 X := SMT_lift _ o.

Definition getRes :=
  let! (_, res) = getState3;
  retn res.

(* We can get a list of the exports by running pass1 (to compute the addresses of labels),
   then this (to grab the exported symbols and their computed address).
 *)
Fixpoint pass_export (addrs: labelmap) (p: program) : ST3 unit :=
  match p with
  | prog_instr c => retn tt
  | prog_data _ _ _ _ c => retn tt
  | prog_skip => retn tt
  | prog_seq p1 p2 =>
      do! pass_export addrs p1;
          pass_export addrs p2
  | prog_declabel g body =>
      let! (labelno, res) = getState3;
      match SF.get addrs labelno with
      | None => lift3 None
      | Some addr =>
          do! setState3 (labelno.+1, if g is Some name then (name, addr) :: res else res);
              pass_export addrs (body addr)
      end
  | prog_label l =>
      retn tt
  end.

Definition get_export (offset : DWORD) (p : program) : option exportList :=
  let addrs := do_pass1 offset p in
  let! (st3, _) = pass_export addrs p (0, nil);
  retn (snd st3).

Definition get_export_safe (offset : DWORD) (p : program) : exportList :=
  if get_export offset p is Some l then l else [::].
