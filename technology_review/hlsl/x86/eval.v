(*===========================================================================
    Instruction evaluator
  ===========================================================================*)
Require Import ssreflect ssrnat ssrbool eqtype tuple. 
Require Import bitsops instr monad reader procstate procstatemonad exn.

Definition updateZPS {n} (result: BITS n) :=  
  do! updateFlagInProcState ZF (result == #0);
  do! updateFlagInProcState PF (lsb result);
  updateFlagInProcState SF (msb result).


Definition evalArithOp {n}
  (f : bool -> BITS _ -> BITS _ -> bool * BITS n) (arg1 arg2: BITS n)  :=
  let! c = getFlagFromProcState CF;
  let (c,result) := f c arg1 arg2 in
  do! updateFlagInProcState CF c;
  do! updateFlagInProcState OF (computeOverflow arg1 arg2 result);
  do! updateZPS result;
  retn result.

Definition evalArithOpNoCarry {n}
  (f : bool -> BITS _ -> BITS _ -> bool * BITS n) (arg1 arg2: BITS n)  :=
  let (c,result) := f false arg1 arg2 in
  do! updateFlagInProcState CF c;
  do! updateFlagInProcState OF (computeOverflow arg1 arg2 result);
  do! updateZPS result;
  retn result.

Definition evalArithUnaryOp {n} (f : BITS n -> bool*BITS n) arg  :=
  let (c,result) := f arg in
  do! updateFlagInProcState CF c;
  do! updateFlagInProcState OF (msb arg != msb result);
  do! updateZPS result;
  retn result.

Definition evalArithUnaryOpNoCarry {n} (f : BITS n -> BITS n) arg  :=  
  let result := f arg in
  do! updateFlagInProcState OF (msb arg != msb result);
  do! updateZPS result;
  retn result.

Definition evalLogicalOp {n} (f : BITS n -> BITS n -> BITS n) arg1 arg2 :=
  let result := f arg1 arg2 in
  do! updateFlagInProcState CF false; 
  do! updateFlagInProcState OF false;
  do! updateZPS result;
  retn result. 

Definition evalBinOp {n} op : BITS n -> BITS n -> ST (BITS n) :=
  match op with
  | OP_ADC => evalArithOp (fun c a b => splitmsb (adcB c a b))
  | OP_ADD => evalArithOpNoCarry (fun c a b => splitmsb (adcB c a b))
  | OP_AND => evalLogicalOp andB
  | OP_OR  => evalLogicalOp orB
  | OP_SBB => evalArithOp sbbB
  | OP_SUB => evalArithOpNoCarry sbbB
  | OP_CMP => evalArithOpNoCarry sbbB
  | OP_XOR => evalLogicalOp xorB
  end.

Definition evalShiftOp {n} (op: ShiftOp)(arg: BITS n.+1) (count:BYTE) : ST (BITS n.+1) :=
  let count := toNat (andB #x"1f" count) in
  (* If the count is zero then no flags are changed, argument is left alone *)
  if count is 0 then retn arg
  else

  (* Otherwise we mess with the carry flag *)
  let! (o, c, res) =
    match op with
    | OP_ROL => let res:= iter count rolB arg 
                in retn (xorb (lsb res) (msb res), lsb res, res)

    | OP_ROR => let res:= iter count rorB arg 
                in retn (xorb (msb res) (msb (dropmsb res)), msb res, res)

    | OP_RCL => let! carry = getFlagFromProcState CF;
                let res:= iter count rolB (joinmsb(carry, arg))
                in retn (xorb (lsb res) (msb res), msb res, dropmsb res)

    | OP_RCR => let! carry = getFlagFromProcState CF;
                let res := iter count rorB (joinlsb(arg, carry))
                in retn (xorb (msb res) (msb (dropmsb res)), lsb res, droplsb res)

    | OP_SHL | OP_SAL => let res:= iter count shlB (joinmsb(false,arg))
                in retn (xorb (msb arg) (msb (dropmsb arg)), msb res, dropmsb res)

    | OP_SHR => let res := iter count shrB (joinlsb(arg,false))
                in retn (msb arg, lsb res, droplsb res)

    | OP_SAR => let res := iter count sarB (joinlsb(arg,false))
                in retn (false, lsb res, droplsb res)
    end;
  do! updateFlagInProcState CF c;
  do! (if count is 1 then updateFlagInProcState CF o else forgetFlagInProcState OF);
  retn res.

Definition evalUnaryOp {n} op : BITS n -> ST (BITS n) :=
  match op with
  | OP_INC => evalArithUnaryOpNoCarry incB
  | OP_DEC => evalArithUnaryOpNoCarry decB
  | OP_NOT => fun arg => retn (invB arg)
(* @todo akenn: Check this, especially carry flag *)
  | OP_NEG => evalArithUnaryOp (fun arg => sbbB false #0 arg)
  end.

Definition evalCondition cc : ST bool :=
  match cc with
  | CC_O => getFlagFromProcState OF
  | CC_B => getFlagFromProcState CF
  | CC_Z => getFlagFromProcState ZF
  | CC_BE => let! cf = getFlagFromProcState CF; let! zf = getFlagFromProcState ZF; retn (cf || zf)
  | CC_S => getFlagFromProcState SF
  | CC_P => getFlagFromProcState PF
  | CC_L => let! sf = getFlagFromProcState SF; let! f = getFlagFromProcState OF; retn (xorb sf f)
  | CC_LE =>
    let! sf = getFlagFromProcState SF; let! f = getFlagFromProcState OF; let! zf = getFlagFromProcState ZF;
    retn ((xorb sf f) || zf)
  end.


Definition scaleBy s (d: DWORD) :=
  match s with
  | S1 => d
  | S2 => shlB d
  | S4 => shlB (shlB d)
  | S8 => shlB (shlB (shlB d))
  end.

(* Evaluation functions for various syntactic entities *)
Definition evalReg (dword:bool) r := 
  let! d = getRegFromProcState r;
  retn (if dword as dword return DWORDorBYTE dword then d else low 8 d).

Definition evalMemSpec m :=
  match m with
    mkMemSpec base ixopt offset =>
    let! baseval = getRegFromProcState base;    
    let p := addB baseval offset in
    match ixopt with
    | None => retn p
    | Some(index,sc) => 
      let! indexval = getRegFromProcState index;
      retn (addB p (scaleBy sc indexval))
    end
  end.

Definition evalSrc src :=
  match src with
  | SrcI c => retn c
  | SrcR r => evalReg true r
  | SrcM m =>  
    let! p = evalMemSpec m; 
    getDWORDFromProcState p
  end.


Definition setDWORDorBYTERegInProcState (dword:bool) (r:Reg) :=
  if dword as dword return DWORDorBYTE dword -> _ then setRegInProcState r else setBYTERegInProcState r.

Definition evalDstR {dword:bool} (drop: bool) (r:Reg) :=
    fun op =>
    let! rval = evalReg dword r;
    let! result = op rval;
    if drop then retn tt else setDWORDorBYTERegInProcState dword r result.

Definition evalDstM (dword:bool) (drop: bool) m 
  (op: DWORDorBYTE dword -> ST (DWORDorBYTE dword)) :=
    let! a = evalMemSpec m;  
    let! v = getDWORDorBYTEFromProcState dword a;
    let! result = op v;
    if drop then retn tt 
    else setDWORDorBYTEInProcState (dword:=dword) a result.

Definition evalDst dword drop dst 
  (op: DWORDorBYTE dword -> ST (DWORDorBYTE dword)) :=
  match dst with
  | RegMemR r => evalDstR drop r op
  | RegMemM m => evalDstM dword drop m op
  end.    

Definition evalRegMem rm :=
  match rm with
  | RegMemR r => evalReg true r
  | RegMemM m => let! a = evalMemSpec m; getDWORDFromProcState a
  end.

Definition evalRegImm {dword} (ri: RegImm dword)  :=
  match ri with
  | RegImmR r => evalReg dword r
  | RegImmI c => retn c
  end.

Definition evalShiftCount (c: ShiftCount) :=
  match c with
  | ShiftCountCL => evalReg false ECX
  | ShiftCountI c => retn c
  end.
  
Definition evalDstSrc {dword} (drop: bool) (ds: DstSrc dword) 
  (op: DWORDorBYTE dword -> DWORDorBYTE dword -> ST (DWORDorBYTE dword)) :=
  match ds with
  | DstSrcRR dst src => 
    evalDstR drop dst (fun a => let! rval = evalReg dword src; op a rval)

  | DstSrcRM dst src => 
    evalDstR drop dst (fun v1 => let! a = evalMemSpec src; 
                                   let! v2 = getDWORDorBYTEFromProcState _ a; op v1 v2)

  | DstSrcMR dst src => 
    evalDstM _ drop dst (fun a => let! rval = evalReg dword src; op a rval)

  | DstSrcRI dst c   => 
    evalDstR drop dst (fun a => op a c)

  | DstSrcMI dst c   => 
    evalDstM _ drop dst (fun a => op a c) 
  end.


Definition evalMOV {dword} (ds: DstSrc dword) :=
  match ds with
  | DstSrcRR dst src => 
    let! v = evalReg dword src; 
    setDWORDorBYTERegInProcState dword dst v

  | DstSrcRM dst src => 
    let! a = evalMemSpec src; 
    let! v = getDWORDorBYTEFromProcState _ a; 
    setDWORDorBYTERegInProcState dword dst v

  | DstSrcMR dst src => 
    let! v = evalReg dword src; 
    let! a = evalMemSpec dst; 
    setDWORDorBYTEInProcState a v

  | DstSrcRI dst v   => 
    setDWORDorBYTERegInProcState dword dst v

  | DstSrcMI dst v   => 
    let! a = evalMemSpec dst; 
    setDWORDorBYTEInProcState a v
  end.


Definition evalPush (v: DWORD) : ST unit :=
  let! oldSP = getRegFromProcState ESP;
  do! setRegInProcState ESP (oldSP-#4);
  setDWORDInProcState (oldSP-#4) v.

Definition evalInstr instr : ST unit :=
  match instr with
  | POP dst =>    
    let! oldSP = getRegFromProcState ESP;
    do! evalDst true false dst (fun d => getDWORDFromProcState oldSP);
    setRegInProcState ESP (oldSP+#4)

  | UOP true op dst => 
    evalDst true false dst (fun d => evalUnaryOp op (d:BITS 32))

  | MOVOP dword ds => 
    evalMOV ds

    (* @todo akenn: implement bit operations *)
  | BITOP op dst b =>
    raiseExn ExnUD

  | BOP dword op ds => 
    evalDstSrc (match op with OP_CMP => true | _ => false end) ds 
    (fun d s => evalBinOp op d s)

  | TESTOP dword dst src =>
    evalDst dword true dst 
    (fun d => let! s = evalRegImm src; evalBinOp OP_AND d s)

  | SHIFTOP true op dst count =>
    evalDst true false dst 
    (fun d => let! c = evalShiftCount count; evalShiftOp (n:=31) op d c)

  | SHIFTOP false op dst count =>
    evalDst false false dst 
    (fun d => let! c = evalShiftCount count; evalShiftOp (n:=7) op d c)

  | IMUL dst src =>
    raiseExn ExnUD

  | MUL src =>
    let! v1 = getRegFromProcState EAX;      
    let! v2 = evalRegMem src;
    let res := mulB v1 v2 in
    let cfof := high 32 res == #0 in
    do! setRegInProcState EAX (low 32 res);
    do! setRegInProcState EDX (high 32 res);
    do! updateFlagInProcState CF cfof;
    do! updateFlagInProcState OF cfof;
    do! forgetFlagInProcState SF;
    do! forgetFlagInProcState PF;
    forgetFlagInProcState ZF    
    
  | LEA r (RegMemM m) => 
    let! a = evalMemSpec m;
    setRegInProcState r a

  | LEA r (RegMemR _) => 
    raiseExn ExnUD

  | JMP src =>
    let! newIP = evalSrc src;
    setRegInProcState EIP newIP

  | JCC cc cv tgt =>
    let! b = evalCondition cc;
    if b == cv then 
      let! oldIP = getRegFromProcState EIP;
      setRegInProcState EIP tgt
    else 
      retn tt

  | CLC =>
    updateFlagInProcState CF false

  | STC =>
    updateFlagInProcState CF true

  | CMC => 
    let! c = getFlagFromProcState CF;
    updateFlagInProcState CF (negb c)

  | HLT =>
    retn tt

  | BADINSTR =>
    raiseExn ExnUD

  | PUSH src =>
    let! v = evalSrc src;
    evalPush v

  | CALL src =>
    let! oldIP = getRegFromProcState EIP;
    let! newIP = evalSrc src;
    do! setRegInProcState EIP newIP; 
    evalPush oldIP

  | RET offset =>
    let! oldSP = getRegFromProcState ESP;
    let! IP' = getDWORDFromProcState oldSP;
    do! setRegInProcState ESP (addB (oldSP+#4) (zeroExtend 16 offset));
    setRegInProcState EIP IP'

  | _ =>
    raiseUnspecified
(*
  | IN dword port =>
    let! d = inputST port;
    setRegInProcState EAX (zeroExtend _ d)

  | OUT dword port =>
    let! eax = getRegFromProcState EAX;
    outputST port (low 8 eax)
*)

  end.

