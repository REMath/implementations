(*===========================================================================
    Encoding of instructions
  ===========================================================================*)
Require Import ssreflect ssrfun ssrbool ssrnat seq tuple eqtype.
Require Import bitsrep bitsops mem reg instr encdechelp writer emb.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* General instruction format is:
     up to four prefix bytes (we don't support these yet)
     one or two opcode bytes

     mod-reg-r/m byte, for register or memory operands, splits up as follows:
       | mod (2 bits) | reg (3 bits) | r/m (3 bits) | 

     SIB byte, if instruction uses scaled indexed memory mode, splits up as follows:
       | scale (2 bits) | index (3 bits) | base (3 bits) |

     displacement (1,2 or 4 bytes) if memory operand includes a displacement
     immediate data (1, 2 or 4 bytes) if instruction has an immediate operand

     Many opcodes include a "direction" bit d to flip src/dst. 
     In table below, opx = opcode extension, s = scale encoding

     dst              src               d mod reg r/m scale index base
     ---              ---               - --- --- --- ----- ----- ----
     R1               R2                0 11  R2  R1
     R1               R2                1 11  R1  R2

     R1               [R2]              1 00  R1  R2
     R1               [R2+disp8]        1 01  R1  R2
     R1               [R2+disp32]       1 10  R1  R2

     R1               [R2+iR*s]         1 00  R1  100  s     iR   R2
     R1               [R2+iR*s+disp8]   1 01  R1  100  s     iR   R2
     R1               [R2+iR*s+disp32]  1 10  R1  100  s     iR   R2

     [R1]             R2                0 00  R2  R1
     [R1+disp8]       R2                0 01  R2  R1
     [R1+disp32]      R2                0 10  R2  R1

     [R1+iR*s]        R2                0 00  R2  100  s     iR   R1
     [R1+iR*s+disp8]  R2                0 01  R2  100  s     iR   R1
     [R1+iR*s+disp32] R2                0 10  R2  100  s     iR   R1

     R                imm/unary           11  opx R    
     [R]              imm/unary           00  opx R
     [R+disp8]        imm/unary           01  opx R
     [R+disp32]       imm/unary           10  opx R
    
     [R+iR*s]         imm/unary           00  opx 100  s     iR   R
     [R+iR*s+disp8]   imm/unary           01  opx 100  s     iR   R
     [R+iR*s+disp32]  imm/unary           10  opx 100  s     iR   R    
*)

Require Import monad.
Notation "w1 $$ w2" := (do! w1; w2) (right associativity, at level 60, only parsing). 

Instance writeRegMem dword : Writer (BITS 3 * RegMem dword) := fun rrm => 
  match rrm with
  | (regbits, RegMemR r) => 
    (writeNext (MODREG ## regbits ## encDWORDorBYTEReg r) $$ retn tt)

  | (regbits, RegMemM (mkMemSpec base optix disp)) =>
    let (encOptSIB,baseBits) := 
      match optix with
      | Some(index,s) => 
        (writeNext (encScale s ## index ## base), SIBRM)

      | None => 
        match base with
        | ESP =>  (writeNext (#b"00" ## #b"100" ## #b"100"), SIBRM)
        | base => (retn tt, base:BITS 3)
        end 
      end
    in 
      if disp == zero _ then  
        writeNext (DISP0  ## regbits ## baseBits) $$
        encOptSIB $$
        retn tt
      else 
      if signTruncate 24 (n:=7) disp is Some b 
      then
        writeNext (DISP8  ## regbits ## baseBits) $$
        encOptSIB $$
        writeNext b $$
        retn tt
      else
        writeNext (DISP32 ## regbits ## baseBits) $$
        encOptSIB $$
        writeNext disp $$
        retn tt
    end.


(* This looks a bit odd but the encode instances in the two branches are different! *)
Definition encodeImm (dword: bool) := 
    if dword as dword return DWORDorBYTE dword -> WriterTm unit
    then writeNext else writeNext.

Definition encodeOpcode (dword:bool) (opcode: BYTE) : WriterTm unit := 
  writeNext (droplsb opcode ## dword). 
 
Definition encodeBOP 
  (dword: bool)
  (srcImmOpcode: BYTE) (srcImmOpx: BITS 3)
  (prefixRM: BITS 5)
  (ds: DstSrc dword)  :=
  match ds with
  | DstSrcRR r1 r2 => 
    writeNext (prefixRM ## #b"01" ## dword) $$
    writeNext (encDWORDorBYTEReg r1, RegMemR dword r2)

  | DstSrcRM r m =>
    writeNext (prefixRM ## #b"01" ## dword) $$
    writeNext (encDWORDorBYTEReg r, RegMemM dword m)

  | DstSrcMR m r =>
    writeNext (prefixRM ## #b"00" ## dword) $$
    writeNext (encDWORDorBYTEReg r, RegMemM dword m)

  | DstSrcRI r c => 
    encodeOpcode dword srcImmOpcode $$
    writeNext (srcImmOpx, RegMemR dword r) $$
    encodeImm c

  | DstSrcMI m c => 
    encodeOpcode dword srcImmOpcode $$
    writeNext (srcImmOpx, RegMemM dword m) $$
    encodeImm c
  end.

Definition encodeUnaryOp dword op : BYTE * BITS 3 * option (BITS 5) :=
  match dword, op with
  | true, OP_INC  => (#x"FF", #0, Some INCPREF)
  | false, OP_INC => (#x"FE", #0, None)
  | true, OP_DEC  => (#x"FF", #1, Some DECPREF)
  | false, OP_DEC => (#x"FE", #1, None)
  | true, OP_NOT  => (#x"F7", #2, None)
  | false, OP_NOT => (#x"F6", #2, None)
  | true, OP_NEG  => (#x"F7", #3, None)
  | false, OP_NEG => (#x"F6", #3, None)
  end.

Definition encodeUOP
  dword
  (op: UnaryOp)
  (dst: RegMem dword) :=
  let: (opcode,opx,regprefix) := encodeUnaryOp dword op in
  writeNext opcode $$
  writeNext (opx, dst).

Require Import cursor.

Instance encodeJumpTarget : Writer Tgt := fun (tgt: Tgt) =>
  let! p = getWCursor;
  let: mkTgt d := tgt in
  if p is mkCursor base 
  then writeNext (subB d (base +# 4)) 
  else writerFail.

(* There seems to be a bug in instance resolution: make sure that any encoding of
   bytes constructed by "pasting" is constrained explicitly to be a BYTE *)
(*=encodeInstr *)
Instance encodeInstr : Writer Instr := fun instr =>
  match instr with
(*=End *)

  (* INC *)
  | UOP dword op dst => 
    encodeUOP op dst
    
  (* PUSH *)
(*=encodePUSH *)
  | PUSH (SrcI c) => 
    if signTruncate 24 (n:=7) c is Some b 
    then do! writeNext #x"6A"; writeNext b
    else do! writeNext #x"68"; writeNext c

  | PUSH (SrcR r) =>
    writeNext (PUSHPREF ## injReg r)

  | PUSH (SrcM src) =>
    do! writeNext #x"FF";
    writeNext (#6, RegMemM true src)
(*=End *)

  (* POP *)
  | POP (RegMemR r) =>
    writeNext (POPPREF ## r)  

  | POP dst =>
    writeNext #x"8F" $$
    writeNext (#0, dst)    

  (* Binary operations *)
  | MOVOP true (DstSrcRI r c) =>
    writeNext (MOVIMMPREF ## r) $$
    encodeImm c

  | MOVOP dword ds => 
    encodeBOP #x"C6" #0 #b"10001" ds

  | MOVX signextend word dst src =>
    writeNext #x"0F" $$
    encodeOpcode word (if signextend then #x"BE" else #x"B6") $$
    writeNext (inj dst, src)

  | TESTOP dword dst (RegImmR src) =>
    encodeOpcode dword #x"84" $$
    writeNext (inj src, dst)
    
  | TESTOP dword dst (RegImmI c) =>
    encodeOpcode dword #x"F6" $$
    writeNext (#0, dst) $$
    encodeImm (dword:=dword) c
    
  | BITOP op dst (RegImmI i) =>
    writeNext #x"0F" $$
    writeNext #x"BA" $$
    writeNext (true ## encBitOp op, dst) $$
    encodeImm i 

  | BITOP op dst (RegImmR r) =>
    writeNext #x"0F" $$
    writeNext (BITOPPREF ## encBitOp op ## BITOPSUFF) $$
    writeNext (inj r, dst)

  | BOP dword op ds => 
    encodeBOP #x"80" (inj op) 
    ((zero 2) ## (inj op)) ds

  | SHIFTOP dword op dst (ShiftCountI c) =>
    if c == #1
    then 
      encodeOpcode dword #x"D0" $$
      writeNext (inj op, dst)
    else
      encodeOpcode dword #x"C0" $$
      writeNext (inj op, dst) $$
      writeNext c

  | SHIFTOP dword op dst ShiftCountCL =>
    encodeOpcode dword #x"D2" $$
    writeNext (inj op, dst)

  | IMUL dst src =>
    writeNext #x"0F" $$
    writeNext #x"AF" $$
    writeNext (inj dst, src)

  | MUL dword src =>
    writeNext (if dword then #x"F7" else #x"F6") $$
    writeNext (#4, src)
 
  | LEA r src => 
    writeNext #x"8D" $$
    writeNext (inj r, src)

  | JCC cc cv tgt =>    
    writeNext #x"0F" $$
    writeNext (JCC32PREF ## encCondition cc ## negb cv) $$
    writeNext (T:=Tgt) tgt 
      
  | CALL (JmpTgtI tgt) =>
    do! writeNext #x"E8";
    writeNext tgt

  | CALL (JmpTgtR r) =>  
    do! writeNext #x"FF";
    writeNext (#2, RegMemR true r)

  | CALL (JmpTgtM m) =>
    do! writeNext #x"FF";
    writeNext (#2, RegMemM true m)

  | JMP (JmpTgtI tgt) =>
    writeNext #x"E9" $$
    writeNext (T:=Tgt) tgt

  | JMP (JmpTgtR r) =>
    writeNext #x"FF" $$
    writeNext (#4, RegMemR true r)

  | JMP (JmpTgtM m) =>
    writeNext #x"FF" $$
    writeNext (#4, RegMemM true m)

  | HLT =>
    writeNext #x"F4"

  | RETOP offset =>
    if offset == zero _ then 
      writeNext #x"C3"
    else 
      writeNext #x"C2" $$
      writeNext offset

  | CMC =>
    writeNext #x"F5"

  | CLC =>
    writeNext #x"F8"

  | STC =>
    writeNext #x"F9"

  | IN dword port =>
    encodeOpcode dword #x"E4" $$
    writeNext port

  | OUT dword port =>
    encodeOpcode dword #x"E6" $$
    writeNext port

    (* Undefined instruction, need for round-tripping *)
  | BADINSTR =>
    writerFail

  end.

