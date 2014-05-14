(*===========================================================================
    Assembler for type [program]. Import this and call [assemble_program].
  ===========================================================================*)
Require Import ssreflect ssrnat seq eqtype tuple.
Require Import tuplehelp bitsrep bitsops mem reg instr instrsyntax encinstr cursor update.
Require Import program monad monadinst.

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
   using the same label twice or destructing label addresses.

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

Definition dummyValue := zero 32.

(* BEWARE: I assume that SF.alloc will allocate addresses in sequential
   order. *)
Fixpoint pass1 (p: program) : @SM state1 unit :=
  match p with
  | prog_instr c =>
      let! (pos, addrs) = SM_get;
      let  bytes := encodeInstr (mkCursor pos) c in
           SM_set (pos +# size bytes, addrs)
  | prog_skip => retn tt
  | prog_seq p1 p2 =>
      do!  pass1 p1;
           pass1 p2
  | prog_declabel body =>
      let! (pos, addrs) = SM_get;
      let: (addrs, labelno) := SF.alloc addrs dummyValue in
      do!  SM_set (pos, addrs);
           pass1 (body #labelno)
  | prog_label l =>
      let! (pos, addrs) = SM_get;
      let  addrs := SF.put addrs (toNat l) pos in
           SM_set (pos, addrs)
  end.

Definition do_pass1 (offset: DWORD) (p: program) : labelmap :=
  let: ((_, addrs), _) := pass1 p (offset, SF.empty) in
  addrs.

(* Current position in memory , label number , code output *)
Definition state2 := (DWORD * nat * seq BYTE)%type.

(* The monad in which pass 2 does its computation. This unfolds to
   fun X => state2 -> option (state2 * X) *)
Definition ST2 := @SMT option state2.

Definition getState2: ST2 state2 := SMT_get _ (S:=_).
Definition setState2: state2 -> ST2 unit := SMT_set _ (S:=_). 
Definition fail2 {X}: ST2 X := SMT_lift _ None.

Fixpoint pass2 (addrs: labelmap) (p: program) : ST2 unit :=
  match p with
  | prog_instr c =>
      let! (pos, labelno, code) = getState2;
      let  bytes := encodeInstr (mkCursor pos) c in
      let: (overflow, pos) := splitmsb (adcB false pos #(size bytes)) in
           if overflow then fail2 else
           (* Possible inefficiency here: we're concatenating with ++. *)
           setState2 (pos, labelno, code ++ bytes)
  | prog_skip => retn tt
  | prog_seq p1 p2 =>
      do!  pass2 addrs p1;
           pass2 addrs p2
  | prog_declabel body =>
      let! (pos, labelno, code) = getState2;
      let! addr = SMT_lift _ (SF.get addrs labelno);
      do!  setState2 (pos, labelno.+1, code);
           pass2 addrs (body addr)
  | prog_label l =>
      let! (pos, _, code) = getState2;
           if pos == l then retn tt else fail2
  end.

Definition do_pass2 (addrs: labelmap) (offset: DWORD) (p: program)
    : option (seq BYTE) :=
  if pass2 addrs p (offset, 0, nil) is Some ((_, _, code), tt)
  then Some code
  else None.

(* This is the main function of the assembler. *)
Definition assemble_program (offset: DWORD) (p: program) : option (seq BYTE) :=
  let addrs := do_pass1 offset p in
  do_pass2 addrs offset p.

(* If a total assembler function is preferred, use the two functions below. *)

Definition assemble_total (offset: DWORD) (p: program) : seq BYTE :=
  match assemble_program offset p with
  | Some code => code
  | None => nil
  end.

Definition assemble_success (offset: DWORD) (p: program) : bool :=
  match assemble_program offset p with
  | Some code => true
  | None => false
  end.
