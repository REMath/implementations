(*===========================================================================
    Decoding of instructions
  ===========================================================================*)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype tuple.
Require Import bitsrep bitsops reg instr mem encdechelp monad reader emb.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* First byte is decoded by a BMAP *)
(* Alternatively, use a custom data structure *)

Definition RegMemToDstSrcI dword dst : DWORDorBYTE dword -> DstSrc dword :=
  match dst with RegMemR r => fun c => DstSrcRI dword r c | RegMemM m => fun c => DstSrcMI dword m c end.

Definition RegMemToDstSrcXR dword rm r :=
  match rm with RegMemR r' => DstSrcRR dword r' r | RegMemM m => DstSrcMR dword m r end.

Definition RegMemToDstSrcRX dword r rm :=
  match rm with RegMemR r' => DstSrcRR dword r r' | RegMemM m => DstSrcRM dword r m end.

Definition RegMemToSrc rm :=
  match rm with RegMemR r => SrcR r | RegMemM m => SrcM m end.

Definition readSIB (rm: BITS 3) : Reader (Reg * option (NonSPReg * Scale)) := 
  if rm == SIBRM then
    let! b = readBYTE;
    match split3 2 3 3 b with
    | (scalebits, ixbits, basebits) =>
      match decNonSPReg ixbits with
      | None => retn (decReg basebits, None)
      | Some ixreg => retn (decReg basebits, Some (ixreg, decScale scalebits))
      end
    end
  else
    retn (decReg rm, None).

(* Regbits might be an operand extension (for unary ops) or a register encoding
   (for binary ops) *)
Definition readRegMem : Reader (BITS 3 * RegMem) :=
  let! b = readBYTE;
  let: (modbits,regbits,rm) := split3 2 3 3 b in
  if modbits == MODREG then 
    retn (regbits, RegMemR (decReg rm))
  else
  if modbits == DISP0 then
    let! (base,ixopt) = readSIB rm;
    retn (regbits, RegMemM (mkMemSpec base ixopt #0))
  else
  if modbits == DISP8 then
    let! (base,ixopt) = readSIB rm;
    let! b = readBYTE;
    retn (regbits, RegMemM (mkMemSpec base ixopt (signExtend 24 b)))
  else (* modbits == DISP32 *)
    let! (base,ixopt) = readSIB rm;
    let! d = readDWORD;
    retn (regbits, RegMemM (mkMemSpec base ixopt d)).

Definition readJumpTarget : Reader DWORD :=
  let! offset = readDWORD;
  let! current = getCursor;
  retn (addB current offset).

Canonical Structure BITS3RegMem_readerType := Eval hnf in mkReaderType readRegMem. 

Open Scope string_scope.
Definition decMap : BYTE -> option (Reader Instr) :=
 [fun _ => None

  with
  #x "05" |-> Some(
    let! c = readDWORD;
    retn (BOP true OP_ADD (DstSrcRI true EAX c))),

  (* Long opcode *)
  #x"0F" |-> Some(
    let! b = readBYTE;
    if b == #x"AF"
    then
      let! (reg,src) = readRegMem;
      retn (IMUL (decReg reg) src)
    else
    
    let (pref,suff) := split2 3 5 b in
    if pref == BITOPPREF
    then 
      if suff == BITIMMSUFF
      then
        let! (opx,dst) = readRegMem;
        let (b,bopx) := split2 1 2 opx in
        if b == #1 then 
          let! c = readBYTE;
          retn (BITOP (decBitOp bopx) dst (RegImmI false c))
        else retn BADINSTR
      else
      let (opx,suff') := split2 2 3 suff in
      if suff' == BITOPSUFF
      then 
        let! (reg,dst) = readRegMem;
        retn (BITOP (decBitOp opx) dst (RegImmR _ (decReg reg)))
      else retn BADINSTR
    else
    let '(pref,suff, cv) := split3 4 3 1 b in
    if pref == JCC32PREF
    then
      let! addr = readJumpTarget;
      retn (JCC (decCondition suff) (negb (thead cv)) addr)
    else
      retn BADINSTR) ,

  #x"68" |-> Some(
    let! c = readDWORD;
    retn (PUSH (SrcI c))),

  #x"80" |-> Some(
    let! (opx,dst) = readRegMem;
    let! c = readBYTE;
    retn (BOP false (decBinOp opx) (RegMemToDstSrcI dst (c: DWORDorBYTE false)))),

  #x"81" |-> Some(
    let! (opx,dst) = readRegMem;
    let! c = readDWORD;
    retn (BOP true (decBinOp opx) (RegMemToDstSrcI dst (c: DWORDorBYTE true)))),

  #x"83" |-> Some(
    let! (opx,dst) = readRegMem;
    let! b = readBYTE;
    retn (BOP true (decBinOp opx) (RegMemToDstSrcI (dword:=true) dst (@signExtend 24 7 b)))),

  #x"84" |-> Some(
    let! (reg,dst) = readRegMem;
    retn (TESTOP false dst (RegImmR _ (decReg reg)))),

  #x"85" |-> Some(
    let! (reg,dst) = readRegMem;
    retn (TESTOP true dst (RegImmR _ (decReg reg)))),

  #x"88" |-> Some(
    let! (reg,dst) = readRegMem;
    retn (MOVOP false (RegMemToDstSrcXR false dst (decReg reg)))),

  #x"89" |-> Some(
    let! (reg,dst) = readRegMem;
    retn (MOVOP true (RegMemToDstSrcXR true dst (decReg reg)))),

  #x"8A" |-> Some(
    let! (reg,src) = readRegMem;
    retn (MOVOP false (RegMemToDstSrcRX false (decReg reg) src))),

  #x"8B" |-> Some(
    let! (reg,src) = readRegMem;
    retn (MOVOP true (RegMemToDstSrcRX true (decReg reg) src))),

  #x"8D" |-> Some(
    let! (reg,src) = readRegMem;
    retn (LEA (decReg reg) src)),

  #x"8F" |-> Some(
    let! (opx,dst) = readRegMem;
    if opx == #b"000"
    then retn (POP dst)
    else retn BADINSTR),

  #x"C0" |-> Some(
    let! (opx,dst) = readRegMem;
    let! c = readBYTE;
    retn (SHIFTOP false (decShiftOp opx) dst (ShiftCountI (c:DWORDorBYTE false)))),

  #x"C1" |-> Some(
    let! (opx,dst) = readRegMem;
    let! c = readBYTE;
    retn (SHIFTOP true (decShiftOp opx) dst (ShiftCountI (c:DWORDorBYTE false)))),

  #x"C2" |-> Some(
    let! offset = readWORD;
    retn (RET offset)),

  #x"C3" |-> Some(
    retn (RET (zero _))),
 
  #x"C6" |-> Some(
    let! (opx,dst) = readRegMem;    
    let! c = readBYTE;
    if opx == #b"000" then retn (MOVOP false (RegMemToDstSrcI dst (c:DWORDorBYTE false)))
    else retn BADINSTR),
    
  #x"C7" |-> Some(
    let! (opx,dst) = readRegMem;    
    let! c = readDWORD;
    if opx == #b"000" then retn (MOVOP true (RegMemToDstSrcI dst (c:DWORDorBYTE true)))
    else retn BADINSTR),
    
  #x"D0" |-> Some(
    let! (opx,dst) = readRegMem;
    retn (SHIFTOP false (decShiftOp opx) dst (ShiftCountI #1))),

  #x"D1" |-> Some(
    let! (opx,dst) = readRegMem;
    retn (SHIFTOP true (decShiftOp opx) dst (ShiftCountI #1))),

  #x"D2" |-> Some(
    let! (opx,dst) = readRegMem;
    retn (SHIFTOP false (decShiftOp opx) dst ShiftCountCL)),

  #x"D3" |-> Some(
    let! (opx,dst) = readRegMem;
    retn (SHIFTOP true (decShiftOp opx) dst ShiftCountCL)),

  #x"E4" |-> Some(
    let! port = readBYTE;
    retn (IN false port)),
 
  #x"E5" |-> Some(
    let! port = readBYTE;
    retn (IN true port)),
 
  #x"E6" |-> Some(
    let! port = readBYTE;
    retn (OUT false port)),
 
  #x"E7" |-> Some(
    let! port = readBYTE;
    retn (OUT true port)),
 
  #x"E8" |-> Some(
    let! addr = readJumpTarget;
    retn (CALL (SrcI addr))),

  #x"E9" |-> Some(
    let! addr = readJumpTarget;
    retn (JMP (SrcI addr))),

  #x"F4" |-> Some(
    retn HLT),

  #x"F5" |-> Some(
    retn CMC),

  #x"F6" |-> Some(
    let! (opx,dst) = readRegMem;
    if opx == #b"000" then
      let! c = readBYTE; 
      retn (TESTOP false dst (RegImmI false c))
    else
    if opx == #b"010" then
      retn (UOP false OP_NOT dst)
    else 
    if opx == #b"011" then
      retn (UOP false OP_NEG dst)
    else
      retn BADINSTR ),

  #x"F7" |-> Some(
    let! (opx,dst) = readRegMem;
    if opx == #b"000" then
      let! c = readDWORD; 
      retn (TESTOP true dst (RegImmI true c))
    else
    if opx == #b"010" then
      retn (UOP true OP_NOT dst)
    else
    if opx == #b"011" then
      retn (UOP true OP_NEG dst)
    else
    if opx == #b"100" then
      retn (MUL dst)
    else retn BADINSTR ),

  #x"F8" |->  Some(
    retn CLC),

  #x"F9" |-> Some(
    retn STC),

  #x"FE" |-> Some(
    let! (opx,dst) = readRegMem;
    if opx == #b"000" then 
      retn (UOP false OP_INC dst)
    else
    if opx == #b"001" then
      retn (UOP false OP_DEC dst)
    else retn BADINSTR),

  #x"FF" |-> Some(
    let! (opx,dst) = readRegMem;
    if opx == #b"000" then
      retn (UOP true OP_INC dst)
    else
    if opx == #b"001" then
      retn (UOP true OP_DEC dst)
    else
    if opx == #b"010" then
      retn (CALL (RegMemToSrc dst))
    else
    if opx == #b"100" then
      retn (JMP (RegMemToSrc dst))
    else
    if opx == #b"110" then
      retn (PUSH (RegMemToSrc dst))
    else retn BADINSTR)].

Definition decodeOtherInstr opcode : Reader Instr :=
  let: (pref,suff) := split2 5 3 opcode in
  if pref == INCPREF then retn (UOP true OP_INC (RegMemR (decReg suff))) else
  if pref == DECPREF then retn (UOP true OP_DEC (RegMemR (decReg suff))) else
  if pref == POPPREF then retn (POP (RegMemR (decReg suff))) else
  if pref == PUSHPREF then retn (PUSH (SrcR (decReg suff))) else
  if pref == MOVIMMPREF then
    let! c = readDWORD;
    retn (MOVOP true (DstSrcRI true (decReg suff) c))
  else let (pref',bop) := split2 2 3 pref
    in if pref' == #b"00" then 
      if suff == #b"001" then       
        let! (reg,dst) = readRegMem;
        retn (BOP true (decBinOp bop) (RegMemToDstSrcXR true dst (decReg reg)))
      else if suff == #b"011" then
        let! (reg,src) = readRegMem;
        retn (BOP true (decBinOp bop) (RegMemToDstSrcRX true (decReg reg) src))
      else if suff == #b"000" then       
        let! (reg,dst) = readRegMem;
        retn (BOP false (decBinOp bop) (RegMemToDstSrcXR false dst (decReg reg)))
      else if suff == #b"010" then
        let! (reg,src) = readRegMem;
        retn (BOP false (decBinOp bop) (RegMemToDstSrcRX false (decReg reg) src))
      else retn BADINSTR
    else retn BADINSTR.

Definition readInstr : Reader Instr :=   
  let! opcode = readBYTE;
  if decMap opcode is Some ri then ri else
  decodeOtherInstr opcode.

Canonical Structure Instr_readerType := Eval hnf in mkReaderType readInstr. 

Definition readInstrs n := @readSeq Instr_readerType n. 

