(* Copyright (c) 2005, Regents of the University of California
 * All rights reserved.
 *
 * Author: Adam Chlipala
 * Extended by: Goran Doychev, Laurent Mauborgne
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 *   this list of conditions and the following disclaimer.
 * - Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * - Neither the name of the University of California, Berkeley nor the names of
 *   its contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR 
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *)

(** The X86 machine language *)

(** {6 Register sets} *)

(** General-purpose 8-bit registers *)
type reg8 =
    AL
  | CL
  | DL
  | BL
  | AH
  | CH
  | DH
  | BH

(** General-purpose 16-bit registers *)
type reg16 =
    AX
  | CX
  | DX
  | BX
  | SP
  | BP
  | SI
  | DI

(** General-purpose 32-bit registers *)
type reg32 =
    EAX
  | ECX
  | EDX
  | EBX
  | ESP (* The stack register *)
  | EBP
  | ESI
  | EDI

let nRegs32 = 8
(** Number of 32-bit registers *)

(** Segment registers *)
type segment_reg =
    ES
  | CS
  | SS
  | DS
  | FS
  | GS

(** Floating-point registers *)
type float_reg =
    ST0
  | ST1
  | ST2
  | ST3
  | ST4
  | ST5
  | ST6
  | ST7

(** MMX registers *)
type mmx_reg =
    MM0
  | MM1
  | MM2
  | MM3
  | MM4
  | MM5
  | MM6
  | MM7

(** Control registers *)
type control_reg =
    CR0
  | CR2
  | CR3
  | CR4

(** Debug registers *)
type debug_reg =
    DR0
  | DR1
  | DR2
  | DR3
  | DR6
  | DR7

(** Test registers *)
type test_reg =
    TR3
  | TR4
  | TR5
  | TR6
  | TR7

(** {6 Flags} *)

(** {6 Condition codes} *)

(** Flags *)
type flag =
  | ID
  | VIP
  | VIF
  | AC
  | VM
  | RF
  | NT
  | IOPL
  | OF
  | DF
  | IF_flag
  | TF
  | SF
  | ZF
  | AF
  | PF
  | CF

(** Basic conditions *)
type condition =
    O  (* Overflow, tested with OF *)
  | B  (* Below,    tested with CF *)
  | Z  (* Zero (or equal), tested with ZF *)
  | BE (* Below or equal, tested with CF v ZF *)
  | S  (* Sign,     tested with SF *)
  | P  (* Parity,   tested with PF *)
  | L  (* Less,     tested with SF<>OF *) (*Less is the signed version of below *)
  | LE (* Less or equal, tested with ZF v (SF<>OF) *)

type cc = bool* condition
(** A condition code is a pair of a basic condition and a boolean indicating 
   whether that condition is true. *)

let nCcs = 16
(** Number of distinct condition codes *)

(** {6 SSE} *)

(** SSE tests *)
type sse =
    SseEQ
  | SseLT
  | SseLE
  | SseUNORD
  | SseNEQ
  | SseNLT
  | SseNLE
  | SseORD

(** {6 Addresses} *)

(** Scales for integer operations *)
type scale =
    Scale1
  | Scale2
  | Scale4
  | Scale8

(** The memory address format supported by the machine language *)
type address =
    {addrDisp : int64;                      (** Constant displacement *)
     addrBase : reg32 option;               (** Optional base register *)
     addrIndex : (scale*reg32) option; (** Optional index register, along
					       with a scaling factor by which to
					       multiply it *)
     segBase : segment_reg option;          (** Optional base segment register *)
   }

(** {6 Operands} *)

(** Generic instruction operands, indexed by the relevant register set *)
type 'a genop =
    Imm of int64       (** A constant machine integer *)
  | Reg of 'a          (** A register *)
  | Address of address (** A memory dereference *)

type op32 = reg32 genop
type op8 = reg8 genop
(** Specializations to particular register sets *)

(** {6 Operations} *)

(** Arithmetic operations *)
type arith_op =
    Add
  | Addc (* Add with carry, meaning adding the carry flag to the result *)
  | And
  | CmpOp  (* Comparison *)
  | Or
  | Sub
  | Subb (* Sub with borrow *)
  | Xor
  (* | ADiv *)
  (* | ARem *)

(** Bitwise shift operations *)
type shift_op =
    Rol
  | Ror
  | Shl
  | Shr
  | Sar

(** The actual instructions.
   These follow the standard x86 instruction set. *)
type instr =
    Arith of arith_op * op32 * op32
  | Arithb of arith_op * op8 * op8
  | Call of op32
  | Cmp of op32 * op32 (* Obtained by substraction of the arguments *)
  | Test of op32 * op32 (* tests the logical AND of the arguments *)
  | Inc of op32
  | Dec of op32
  | Jcc of cc * int64
  | Jmp of op32
  | Lea of reg32 * address
  (* | Div of op32 *)
  | Leave
  | Mov of op32 * op32
  | Movb of op8 * op8
  | Movzx of op32 * op8
  | Exchange of reg32 * reg32
  | Pop of op32
  | Push of op32
  | Ret
  | Shift of shift_op * op32 * op8
  | Halt
  | Skip
  | FlagSet of flag*bool (*sets the flag to the bool value *)

