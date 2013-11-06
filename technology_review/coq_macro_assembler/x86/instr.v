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


(* Memory addressing. Note: using ESP for the index register is illegal *)
(*=MemSpec *)
Inductive Scale := S1 | S2 | S4 | S8.
Inductive MemSpec :=
  mkMemSpec (base: Reg) 
            (indexAndScale: option (NonSPReg*Scale)) 
            (offset: DWORD).
(*=End *)

(* 8-bit register *)
(*=BYTEReg *)
Inductive BYTEReg := 
| AL | CL | DL | BL | AH | CH | DH | BH.
Definition DWORDorBYTEReg (d: bool) := 
  if d then Reg else BYTEReg.
(*=End *)

(* Register or memory *)
(*=RegMem *)
Inductive RegMem d := 
| RegMemR :> DWORDorBYTEReg d -> RegMem d
| RegMemM :> MemSpec -> RegMem d.
(*=End *)

Coercion mkRegMemR (r:Reg) := RegMemR true r.

(* Register or immediate *)
Inductive RegImm dword :=
| RegImmI :> DWORDorBYTE dword -> RegImm dword
| RegImmR :> DWORDorBYTEReg dword -> RegImm dword.

(* Unary ops: immediate, register, or memory source *)
(* Binary ops: five combinations of source and destination *)
(*=Src *)
Inductive Src :=
| SrcI :> DWORD -> Src 
| SrcM :> MemSpec -> Src
| SrcR :> Reg -> Src.
Inductive DstSrc (d: bool) :=
| DstSrcRR (dst src: DWORDorBYTEReg d)
| DstSrcRM (dst: DWORDorBYTEReg d) (src: MemSpec)
| DstSrcMR (dst: MemSpec) (src: DWORDorBYTEReg d)
| DstSrcRI (dst: DWORDorBYTEReg d) (c: DWORDorBYTE d)
| DstSrcMI (dst: MemSpec) (c: DWORDorBYTE d).
(*=End *)
(* Jump target *)
(* We make this a separate type constructor to pick up type class instances later *)
(* Jump ops: immediate, register, or memory source *)
(*=Tgt *)
Inductive Tgt := 
| mkTgt :> DWORD -> Tgt.
Inductive JmpTgt :=
| JmpTgtI :> Tgt -> JmpTgt
| JmpTgtM :> MemSpec -> JmpTgt
| JmpTgtR :> Reg -> JmpTgt.
(*=End *)
Inductive ShiftCount :=
| ShiftCountCL
| ShiftCountI (c: BYTE).


(* All binary operations come in byte and dword flavours, specified in the instruction *)
(* Unary operations come in byte and dword flavours, except for POP *)
(*=BinOp *)
Inductive BinOp := 
| OP_ADC | OP_ADD | OP_AND | OP_CMP 
| OP_OR | OP_SBB | OP_SUB | OP_XOR.
Inductive UnaryOp := 
| OP_INC | OP_DEC | OP_NOT | OP_NEG.
(*=End *)
Inductive BitOp :=
| OP_BT | OP_BTC | OP_BTR | OP_BTS.

Inductive ShiftOp :=
| OP_ROL | OP_ROR | OP_RCL | OP_RCR
| OP_SHL | OP_SHR | OP_SAL | OP_SAR.

(*=Condition *)
Inductive Condition := 
| CC_O | CC_B | CC_Z | CC_BE | CC_S | CC_P | CC_L | CC_LE.
(*=End *)

(* dword=true if 32-bits, dword=false if 8-bits *)
(*=Instr *)
Inductive Instr :=
| UOP d (op: UnaryOp) (dst: RegMem d)
| BOP d (op: BinOp ) (ds: DstSrc d)
| BITOP (op: BitOp) (dst: RegMem true) (bit: RegImm false)
| TESTOP d (dst: RegMem d) (src: RegImm d)
| MOVOP d (ds: DstSrc d)
| MOVX (signextend:bool) (w: bool) (dst: Reg) (src: RegMem w)
| SHIFTOP d (op: ShiftOp) (dst: RegMem d) (count: ShiftCount)
| MUL {d} (src: RegMem d)
| IMUL (dst: Reg) (src: RegMem true) 
| LEA (reg: Reg) (src: RegMem true) 
| JCC (cc: Condition) (cv: bool) (tgt: Tgt)
| PUSH (src: Src)
| POP (dst: RegMem true)
| CALL (tgt: JmpTgt) | JMP (tgt: JmpTgt)
| CLC | STC | CMC
| RETOP (size: WORD)
| OUT (d: bool) (port: BYTE)
| IN (d: bool) (port: BYTE)
| HLT | BADINSTR.
(*=End *)


