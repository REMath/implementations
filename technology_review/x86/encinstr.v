(*===========================================================================
    Encoding of instructions
  ===========================================================================*)
Require Import ssreflect ssrfun ssrbool ssrnat seq tuple eqtype.
Require Import bitsrep bitsops mem reg instr encdechelp enc emb.

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

(*(* Basic definitions for the writer *)
Definition Writer T := seq BYTE -> T * seq BYTE.

Instance writerMonad : Monad Writer :=
{ ret := fun {X} (x:X) s => (x,s)
; bind := fun {X Y} (m: Writer X) f s => let (r,s') := m s in f r s' }.
(*Proof. intros. destruct (f x). apply functional_extensionality. auto. 
intros. apply functional_extensionality. intros. destruct (c x); auto. 
intros. apply functional_extensionality. intros. destruct (c x); auto. 
Qed. *)
*)

Instance encodeRegMem : Encoder (BITS 3 * RegMem) := fun rrm =>
  match rrm with
  | (regbits, RegMemR r) => 
    encode (MODREG ## regbits ## r)

  | (regbits, RegMemM (mkMemSpec base optix disp)) =>
    let (encOptSIB,baseBits) := 
      match optix with
      | Some(index,s) => 
        (encode (encScale s ## index ## base), SIBRM)

      | None => 
        match base with
        | ESP =>  (encode (#b"00" ## #b"100" ## #b"100"), SIBRM)
        | base => ([::], base:BITS 3)
        end 
      end
    in 
      if disp == zero _ then  
        encode (DISP0  ## regbits ## baseBits) ++
        encOptSIB
      else 
      if signTruncate 24 (n:=7) disp is Some b 
      then
        encode (DISP8  ## regbits ## baseBits) ++
        encOptSIB ++
        encode b
      else
        encode (DISP32 ## regbits ## baseBits) ++
        encOptSIB ++
        encode disp
    end.

(* This looks a bit odd but the encode instances in the two branches are different! *)
Definition encodeImm (dword: bool) := 
    if dword as dword return DWORDorBYTE dword -> seq BYTE 
    then encode else encode.

Definition encodeOpcode (dword:bool) (opcode: BYTE) : seq BYTE := 
  encode (droplsb opcode ## dword : BYTE).
 
Definition encodeBOP 
  (dword: bool)
  (srcImmOpcode: BYTE) (srcImmOpx: BITS 3)
  (prefixRM: BITS 5)
  (ds: DstSrc dword)  :=
  match ds with
  | DstSrcRR r1 r2 => 
    encode (prefixRM ## #b"01" ## dword) ++
    encode (inj r1, RegMemR r2)

  | DstSrcRM r m =>
    encode (prefixRM ## #b"01" ## dword) ++
    encode (inj r, RegMemM m)

  | DstSrcMR m r =>
    encode (prefixRM ## #b"00" ## dword) ++ 
    encode (inj r, RegMemM m)

  | DstSrcRI r c => 
    encodeOpcode dword srcImmOpcode ++
    encode (srcImmOpx, RegMemR r) ++
    encodeImm c

  | DstSrcMI m c => 
    encodeOpcode dword srcImmOpcode ++
    encode (srcImmOpx, RegMemM m) ++
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
  (dst: RegMem) :=
  let: (opcode,opx,regprefix) := encodeUnaryOp dword op in
  encode opcode ++
  encode (opx, dst).

Require Import cursor.

Definition encodeRel (tgt: DWORD) (p: Cursor 32) := 
  encode (if p is mkCursor base then subB tgt (base +# 4) else #0).

(* There seems to be a bug in instance resolution: make sure that any encoding of
   bytes constructed by "pasting" is constrained explicitly to be a BYTE *)
Instance encodeInstr (addr: Cursor 32) : Encoder Instr := fun instr =>
  match instr with

  (* INC *)
  | UOP dword op dst => 
    encodeUOP dword op dst
    
  (* PUSH *)
  | PUSH (SrcI c) =>
    encode #x"68" ++
    encode c

  | PUSH (SrcR r) =>
    encode (PUSHPREF ## r)

  | PUSH (SrcM src) =>
    encode #x"FF" ++
    encode (#6, RegMemM src)

  (* POP *)
  | POP dst =>
    encode #x"8F" ++
    encode (#0, dst)    

  (* Binary operations *)
  | MOVOP true (DstSrcRI r c) =>
    encode (MOVIMMPREF ## r) ++
    encode c

  | MOVOP dword ds => 
    encodeBOP #x"C6" #0 #b"10001" ds

  | TESTOP dword dst (RegImmR src) =>
    encodeOpcode dword #x"84" ++
    encode (inj src, dst)
    
  | TESTOP dword dst (RegImmI c) =>
    encodeOpcode dword #x"F6" ++
    encode (#0, dst) ++
    encodeImm (dword:=dword) c
    
  | BITOP op dst (RegImmI i) =>
    encode #x"0F" ++ 
    encode #x"BA" ++
    encode (true ## encBitOp op, dst) ++  
    encode i 

  | BITOP op dst (RegImmR r) =>
    encode #x"0F" ++
    encode (BITOPPREF ## encBitOp op ## BITOPSUFF) ++
    encode (inj r, dst)

  | BOP dword op ds => 
    encodeBOP #x"80" (inj op) 
    ((zero 2) ## (inj op)) ds

  | SHIFTOP dword op dst (ShiftCountI c) =>
    if c == #1
    then 
      encodeOpcode dword #x"D0" ++
      encode (inj op, dst)
    else
      encodeOpcode dword #x"C0" ++
      encode (inj op, dst) ++
      encode c

  | SHIFTOP dword op dst ShiftCountCL =>
    encodeOpcode dword #x"D2" ++
    encode (inj op, dst)

  | IMUL dst src =>
    encode #x"0F" ++
    encode #x"AF" ++
    encode (inj dst, src)

  | MUL src =>
    encode #x"F7" ++ 
    encode (#4, src)
 
  | LEA r src => 
    encode #x"8D" ++
    encode (inj r, src)

  | JCC cc cv tgt =>    
    encode #x"0F" ++
    encode (JCC32PREF ## encCondition cc ## negb cv) ++
    encodeRel tgt (nextCursor (nextCursor addr))
      
  | CALL (SrcI tgt) =>
    encode #x"E8" ++
    encodeRel tgt (nextCursor addr)

  | CALL (SrcR r) =>
    encode #x"FF" ++
    encode (#2, RegMemR r)

  | CALL (SrcM m) =>
    encode #x"FF" ++
    encode (#2, RegMemM m)

  | JMP (SrcI tgt) =>
    encode #x"E9" ++
    encodeRel tgt (nextCursor addr)

  | JMP (SrcR r) =>
    encode #x"FF" ++
    encode (#4, RegMemR r)

  | JMP (SrcM m) =>
    encode #x"FF" ++
    encode (#4, RegMemM m)

  | HLT =>
    encode #x"F4"

  | RET offset =>
    if offset == zero _ then 
      encode #x"C3"
    else 
      encode #x"C2" ++ 
      encode offset

  | CMC =>
    encode #x"F5"

  | CLC =>
    encode #x"F8"

  | STC =>
    encode #x"F9"

  | IN dword port =>
    encodeOpcode dword #x"E4" ++
    encode port

  | OUT dword port =>
    encodeOpcode dword #x"E6" ++
    encode port

    (* Undefined instruction, need for round-tripping *)
  | BADINSTR =>
    encode #x"D6"

  end.

