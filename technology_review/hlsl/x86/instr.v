(*===========================================================================
    Instruction type and helpers
    Instructions abstract the actual machine-code encoding in a number of ways:
    (a) There may be more than one way of encoding the same instruction
        e.g. short forms and long forms
    (b) Jump and call targets are recorded as absolute addresses but might be
        encoded as relative offsets.
    Instructions therefore are *not* position-independent.
  ===========================================================================*)
Require Import bitsrep reg.

CoInductive Scale := S1 | S2 | S4 | S8.

(* Memory addressing. Note: using ESP for the index register is illegal *)
Inductive MemSpec :=
  mkMemSpec (base: Reg) 
            (indexAndScale: option (NonSPReg*Scale)) 
            (offset: DWORD).

(* Register or memory *)
Inductive RegMem := 
| RegMemR :> Reg -> RegMem
| RegMemM :> MemSpec -> RegMem.

(* Register or immediate *)
Inductive RegImm dword :=
| RegImmI (c: DWORDorBYTE dword)
| RegImmR (r: Reg).

(* Unary ops: immediate, register, or memory source *)
Inductive Src :=
| SrcI :> DWORD -> Src
| SrcM :> MemSpec -> Src
| SrcR :> Reg -> Src.

Inductive ShiftCount :=
| ShiftCountCL
| ShiftCountI (c: BYTE).

(* Binary ops: five combinations of source and destination *)
(* Source to destination *)
Inductive DstSrc (dword: bool) :=
| DstSrcRR (dst src: Reg)
| DstSrcRM (dst: Reg) (src: MemSpec)
| DstSrcMR (dst: MemSpec) (src: Reg)
| DstSrcRI (dst: Reg) (c: DWORDorBYTE dword)
| DstSrcMI (dst: MemSpec) (c: DWORDorBYTE dword).

(* Jump target: an actual (relative) offset, or a label *)
Definition Tgt := DWORD.

(* All binary operations come in byte and dword flavours, specified in the instruction *)
Inductive BinOp := 
| OP_ADC | OP_ADD | OP_AND | OP_CMP | OP_OR | OP_SBB | OP_SUB | OP_XOR.

(* Unary operations come in byte and dword flavours, except for POP *)
Inductive UnaryOp := 
| OP_INC | OP_DEC | OP_NOT | OP_NEG.

Inductive BitOp :=
| OP_BT | OP_BTC | OP_BTR | OP_BTS.

Inductive ShiftOp :=
| OP_ROL | OP_ROR | OP_RCL | OP_RCR
| OP_SHL | OP_SHR | OP_SAL | OP_SAR.

Inductive Condition := 
| CC_O | CC_B | CC_Z | CC_BE | CC_S | CC_P | CC_L | CC_LE.

(* dword=true if 32-bits, dword=false if 8-bits *)
Inductive Instr : Type :=
| UOP (dword: bool) (op: UnaryOp) (dst: RegMem)
| BOP (dword: bool) (op: BinOp ) (ds: DstSrc dword)
| BITOP (op: BitOp) (dst: RegMem) (bit: RegImm false)
| TESTOP (dword: bool) (dst: RegMem) (src: RegImm dword)
| MOVOP (dword: bool) (ds: DstSrc dword)
| SHIFTOP (dword: bool) (op: ShiftOp) (dst: RegMem) (count: ShiftCount)
| MUL (src: RegMem)
| IMUL (dst: Reg) (src: RegMem)
| LEA (reg: Reg) (src: RegMem) 
| JCC (cc: Condition) (cv: bool) (tgt: Tgt)
| PUSH (src: Src)
| POP (dst: RegMem)
| CALL (src: Src)
| JMP (src: Src)
| CLC | STC | CMC
| RET (size: WORD)
| HLT
| OUT (dword: bool) (port: BYTE)
| IN (dword: bool) (port: BYTE)
| BADINSTR.

(* True if this is a control-flow instruction of any kind. All other instructions
   merely advance EIP to the next instruction *)
Definition mayBranch (i:Instr) :=
  match i with
  | JCC _ _ _ | CALL _ | JMP _ | RET _ => true
  | _ => false
  end.


