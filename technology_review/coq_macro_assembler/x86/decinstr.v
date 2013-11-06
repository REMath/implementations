(*===========================================================================
    Decoding of instructions
  ===========================================================================*)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype tuple.
Require Import bitsrep bitsops reg instr mem encdechelp monad reader cursor emb.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition RegMemToDstSrcI dword dst : DWORDorBYTE dword -> DstSrc dword :=
  match dst with RegMemR r => fun c => DstSrcRI dword r c | RegMemM m => fun c => DstSrcMI dword m c end.

Definition RegMemToDstSrcXR dword rm r :=
  match rm with RegMemR r' => DstSrcRR dword r' r | RegMemM m => DstSrcMR dword m r end.

Definition RegMemToDstSrcRX dword r rm :=
  match rm with RegMemR r' => DstSrcRR dword r r' | RegMemM m => DstSrcRM dword r m end.

Definition RegMemToSrc (rm: RegMem true)  :=
  match rm with RegMemR r => SrcR r | RegMemM m => SrcM m end.

Definition RegMemToJmpTgt (rm: RegMem true) :=
  match rm with RegMemR r => JmpTgtR r | RegMemM m => JmpTgtM m end.

Definition readSIB (rm: BITS 3) : Reader (Reg * option (NonSPReg * Scale)) := 
  if rm == SIBRM then
    let! b = readNext;
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
Instance readRegMem dword : Reader (BITS 3 * RegMem dword) :=
  let! b = readNext;
  let: (modbits,regbits,rm) := split3 2 3 3 b in
  if modbits == MODREG then 
    retn (regbits, RegMemR dword (decDWORDorBYTEReg dword rm))
  else
  if modbits == DISP0 then
    let! (base,ixopt) = readSIB rm;
    retn (regbits, RegMemM dword (mkMemSpec base ixopt #0))
  else
  if modbits == DISP8 then
    let! (base,ixopt) = readSIB rm;
    let! b = readNext (T:=BYTE);
    retn (regbits, RegMemM dword (mkMemSpec base ixopt (signExtend 24 b)))
  else (* modbits == DISP32 *)
    let! (base,ixopt) = readSIB rm;
    let! d = readNext;
    retn (regbits, RegMemM dword (mkMemSpec base ixopt d)).

(* First byte is decoded by a BMAP *)
(* Alternatively, use a custom data structure *)

Instance readJumpTarget : Reader Tgt :=
  let! current = readCursor;
  let! offset = readNext (T:=DWORD);
  if current is mkCursor p then retn (mkTgt (addB (p+#4) offset)) else retn (mkTgt #0).

Open Scope string_scope.
Definition decMap : BYTE -> option (Reader Instr) :=
 [fun _ => None

  with
  #x "05" |-> Some(
    let! c = readNext;
    retn (BOP true OP_ADD (DstSrcRI true EAX c))),

  (* Long opcode *)
  #x"0F" |-> Some(
    let! b = readNext;
    if b == #x"AF"
    then
      let! (reg,src) = readNext;
      retn (IMUL (decReg reg) src)
    else

    if b == #x"B6" 
    then 
      let! (dst,src) = readNext;
      retn (MOVX false false (decReg dst) src)
    else

    if b == #x"B7" 
    then 
      let! (dst,src) = readNext;
      retn (MOVX false true (decReg dst) src)
    else

    if b == #x"BE" 
    then 
      let! (dst,src) = readNext;
      retn (MOVX true false (decReg dst) src)
    else

    if b == #x"BF" 
    then 
      let! (dst,src) = readNext;
      retn (MOVX true true (decReg dst) src)
    else

    let (pref,suff) := split2 3 5 b in
    if pref == BITOPPREF
    then 
      if suff == BITIMMSUFF
      then
        let! (opx,dst) = readNext;
        let (b,bopx) := split2 1 2 opx in
        if b == #1 then 
          let! c = readNext;
          retn (BITOP (decBitOp bopx) dst (RegImmI false c))
        else retn BADINSTR
      else
      let (opx,suff') := split2 2 3 suff in
      if suff' == BITOPSUFF
      then 
        let! (reg,dst) = readNext;
        retn (BITOP (decBitOp opx) dst (RegImmR false (decDWORDorBYTEReg false reg)))
      else retn BADINSTR
    else
    let '(pref,suff, cv) := split3 4 3 1 b in
    if pref == JCC32PREF
    then
      let! addr = readNext (T:=Tgt);
      retn (JCC (decCondition suff) (negb (thead cv)) addr)
    else
      retn BADINSTR) ,

  #x"68" |-> Some(
    let! c = readNext;
    retn (PUSH (SrcI c))),

  #x"6A" |-> Some(
    let! c = readNext;
    retn (PUSH (SrcI (@signExtend 24 7 c)))),

  #x"80" |-> Some(
    let! (opx,dst) = readNext;
    let! c = readNext;
    retn (BOP false (decBinOp opx) (RegMemToDstSrcI dst (c: DWORDorBYTE false)))),

  #x"81" |-> Some(
    let! (opx,dst) = readNext;
    let! c = readNext;
    retn (BOP true (decBinOp opx) (RegMemToDstSrcI dst (c: DWORDorBYTE true)))),

   #x"83" |-> Some(
    let! (opx,dst) = readNext;
    let! b = readNext;
    retn (BOP true (decBinOp opx) (RegMemToDstSrcI (dword:=true) dst (@signExtend 24 7 b)))),

  #x"84" |-> Some(
    let! (reg,dst) = readNext;
    retn (TESTOP false dst (RegImmR _ (decDWORDorBYTEReg _ reg)))),

  #x"85" |-> Some(
    let! (reg,dst) = readNext;
    retn (TESTOP true dst (RegImmR _ (decDWORDorBYTEReg _ reg)))),

  #x"88" |-> Some(
    let! (reg,dst) = readNext;
    retn (MOVOP false (RegMemToDstSrcXR dst (decDWORDorBYTEReg _ reg)))),

  #x"89" |-> Some(
    let! (reg,dst) = readNext;
    retn (MOVOP true (RegMemToDstSrcXR dst (decDWORDorBYTEReg _ reg)))),

  #x"8A" |-> Some(
    let! (reg,src) = readNext;
    retn (MOVOP false (RegMemToDstSrcRX (decDWORDorBYTEReg _ reg) src))),

  #x"8B" |-> Some(
    let! (reg,src) = readNext;
    retn (MOVOP true (RegMemToDstSrcRX (decDWORDorBYTEReg _ reg) src))),

  #x"8D" |-> Some(
    let! (reg,src) = readNext;
    retn (LEA (decReg reg) src)),

  #x"8F" |-> Some(
    let! (opx,dst) = readNext;
    if opx == #b"000"
    then retn (POP dst)
    else retn BADINSTR),

  #x"C0" |-> Some(
    let! (opx,dst) = readNext;
    let! c = readNext;
    retn (SHIFTOP false (decShiftOp opx) dst (ShiftCountI (c:DWORDorBYTE false)))),

  #x"C1" |-> Some(
    let! (opx,dst) = readNext;
    let! c = readNext;
    retn (SHIFTOP true (decShiftOp opx) dst (ShiftCountI (c:DWORDorBYTE false)))),

  #x"C2" |-> Some(
    let! offset = readNext;
    retn (RETOP offset)),

  #x"C3" |-> Some(
    retn (RETOP (zero _))),
 
  #x"C6" |-> Some(
    let! (opx,dst) = readNext;    
    let! c = readNext;
    if opx == #b"000" then retn (MOVOP false (RegMemToDstSrcI dst (c:DWORDorBYTE false)))
    else retn BADINSTR),
    
  #x"C7" |-> Some(
    let! (opx,dst) = readNext;    
    let! c = readNext;
    if opx == #b"000" then retn (MOVOP true (RegMemToDstSrcI dst (c:DWORDorBYTE true)))
    else retn BADINSTR),
    
  #x"D0" |-> Some(
    let! (opx,dst) = readNext;
    retn (SHIFTOP false (decShiftOp opx) dst (ShiftCountI #1))),

  #x"D1" |-> Some(
    let! (opx,dst) = readNext;
    retn (SHIFTOP true (decShiftOp opx) dst (ShiftCountI #1))),

  #x"D2" |-> Some(
    let! (opx,dst) = readNext;
    retn (SHIFTOP false (decShiftOp opx) dst ShiftCountCL)),

  #x"D3" |-> Some(
    let! (opx,dst) = readNext;
    retn (SHIFTOP true (decShiftOp opx) dst ShiftCountCL)),

  #x"E4" |-> Some(
    let! port = readNext;
    retn (IN false port)),
 
  #x"E5" |-> Some(
    let! port = readNext;
    retn (IN true port)),
 
  #x"E6" |-> Some(
    let! port = readNext;
    retn (OUT false port)),
 
  #x"E7" |-> Some(
    let! port = readNext;
    retn (OUT true port)),
 
  #x"E8" |-> Some(
    let! addr = readNext (T:=Tgt);
    retn (CALL (JmpTgtI addr))),

  #x"E9" |-> Some(
    let! addr = readNext (T:=Tgt);
    retn (JMP (JmpTgtI addr))),

  #x"F4" |-> Some(
    retn HLT),

  #x"F5" |-> Some(
    retn CMC),

  #x"F6" |-> Some(
    let! (opx,dst) = readNext;
    if opx == #b"000" then
      let! c = readNext; 
      retn (TESTOP false dst (RegImmI false c))
    else
    if opx == #b"010" then
      retn (UOP false OP_NOT dst)
    else 
    if opx == #b"011" then
      retn (UOP false OP_NEG dst)
    else
    if opx == #b"100" then
      retn (@MUL false dst)
    else
      retn BADINSTR ),

  #x"F7" |-> Some(
    let! (opx,dst) = readNext;
    if opx == #b"000" then
      let! c = readNext; 
      retn (TESTOP true dst (RegImmI true c))
    else
    if opx == #b"010" then
      retn (UOP true OP_NOT dst)
    else
    if opx == #b"011" then
      retn (UOP true OP_NEG dst)
    else
    if opx == #b"100" then
      retn (@MUL true dst)
    else retn BADINSTR ),

  #x"F8" |->  Some(
    retn CLC),

  #x"F9" |-> Some(
    retn STC),

  #x"FE" |-> Some(
(*=decINCDEC *)
    let! (opx,dst) = readNext;
    if opx == #b"000" then 
      retn (UOP false OP_INC dst)
    else
    if opx == #b"001" then
      retn (UOP false OP_DEC dst)
    else retn BADINSTR),
(*=End *)

  #x"FF" |-> Some(
    let! (opx,dst) = readNext;
    if opx == #b"000" then
      retn (UOP true OP_INC dst)
    else
    if opx == #b"001" then
      retn (UOP true OP_DEC dst)
    else
    if opx == #b"010" then
      retn (CALL (RegMemToJmpTgt dst))
    else
    if opx == #b"100" then
      retn (JMP (RegMemToJmpTgt dst))
    else
    if opx == #b"110" then
      retn (PUSH (RegMemToSrc dst))
    else retn BADINSTR)].

Definition decodeOtherInstr opcode : Reader Instr :=
  let: (pref,suff) := split2 5 3 opcode in
  if pref == INCPREF then retn (UOP true OP_INC (RegMemR _ (decDWORDorBYTEReg _ suff))) else
  if pref == DECPREF then retn (UOP true OP_DEC (RegMemR _ (decDWORDorBYTEReg _ suff))) else
  if pref == POPPREF then retn (POP (RegMemR _ (decDWORDorBYTEReg _ suff))) else
  if pref == PUSHPREF then retn (PUSH (SrcR (decReg suff))) else
  if pref == MOVIMMPREF then
    let! c = readNext;
    retn (MOVOP true (DstSrcRI true (decReg suff) c))
  else let (pref',bop) := split2 2 3 pref
    in if pref' == #b"00" then 
      if suff == #b"001" then       
        let! (reg,dst) = readNext;
        retn (BOP true (decBinOp bop) (RegMemToDstSrcXR dst (decDWORDorBYTEReg _ reg)))
      else if suff == #b"011" then
        let! (reg,src) = readNext;
        retn (BOP true (decBinOp bop) (RegMemToDstSrcRX (decDWORDorBYTEReg _ reg) src))
      else if suff == #b"000" then       
        let! (reg,dst) = readNext;
        retn (BOP false (decBinOp bop) (RegMemToDstSrcXR dst (decDWORDorBYTEReg _ reg)))
      else if suff == #b"010" then
        let! (reg,src) = readNext;
        retn (BOP false (decBinOp bop) (RegMemToDstSrcRX (decDWORDorBYTEReg _ reg) src))
      else retn BADINSTR
    else retn BADINSTR.

Instance readInstr : Reader Instr :=
  let! opcode = readNext;
  if decMap opcode is Some ri then ri else
  decodeOtherInstr opcode.

(*
Definition jmpDecoder : Reader Instr := 
    let! addr = readJumpTarget;
    retn (JMP (SrcI addr)).

Lemma decode_JMP_inversion (p:DWORD) bs q bs' d : 
  runReader readInstr p bs = Some (q, bs', JMP d)  ->
  exists bs'': seq BYTE, bs = #x"E9" :: bs'' /\
  runReader jmpDecoder (next p) bs'' = Some (q, bs', JMP d).
Proof. move => H. 
destruct bs => //. 
exists bs. simpl in H. 
case E: (b == #x "E9"). 
rewrite (eqP E) in H.
set DM:= decMap _ in H. hnf in DM.
subst DM. 
cbv iota in H.
rewrite /jmpDecoder. split. by rewrite (eqP E). 
done. 
Qed.

*)