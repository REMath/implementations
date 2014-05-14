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

(* Pretty-printing *)

open Format
open X86Types
open X86Util

exception Print of string

type 'a printer = formatter -> 'a -> unit




let pp_addr fmt n = pp_print_string fmt (Printf.sprintf "0x%Lx" n)
let pp_int32 fmt n = pp_print_string fmt (Int32.to_string n)


(*** A dity way to deal with negative integers; 
     this shouldn't be done here but in read_int***)
(*let high_bit_8 = Int64.shift_left Int64.one 7
let higher_bit_8 = Int64.shift_left Int64.one 8
let pp_int8 fmt n =
  if Int64.logand n high_bit_8 = Int64.zero then
    pp_print_string fmt (Int64.to_string n)
  else
    fprintf fmt "-%Ld" (Int64.sub higher_bit_8 n)*)

(*let high_bit = Int64.shift_left Int64.one 31 
let higher_bit = Int64.shift_left Int64.one 32*)
let pp_int64 fmt n =
    fprintf fmt "%Ld" n
  (*if Int64.logand n high_bit = Int64.zero then
    fprintf fmt "%Ld" n
  else
    fprintf fmt "-%Ld" (Int64.sub higher_bit n)*)

let pp_reg8 fmt r = pp_print_string fmt (reg8_to_string r)
let pp_reg16 fmt r = pp_print_string fmt (reg16_to_string r)
let pp_reg32 fmt r = pp_print_string fmt (reg32_to_string r)
let pp_segment_reg fmt r = pp_print_string fmt (segment_reg_to_string r)
let pp_float_reg fmt r = pp_print_string fmt (float_reg_to_string r)
let pp_mmx_reg fmt r = pp_print_string fmt (mmx_reg_to_string r)
let pp_control_reg fmt r = pp_print_string fmt (control_reg_to_string r)
let pp_debug_reg fmt r = pp_print_string fmt (debug_reg_to_string r)
let pp_test_reg fmt r = pp_print_string fmt (test_reg_to_string r)

let pp_flag fmt f =
  Format.fprintf fmt "%s"
    (match f with
    | ID -> "ID"
    | VIP -> "VIP"
    | VIF -> "VIF"
    | AC -> "AC"
    | VM -> "VM"
    | RF -> "RF"
    | NT -> "NT"
    | IOPL -> "IOPL"
    | OF -> "OF"
    | DF -> "DF"
    | IF_flag -> "IF"
    | TF -> "TF"
    | SF -> "SF"
    | ZF -> "ZF"
    | AF -> "AF"
    | PF -> "PF"
    | CF -> "CF")

let pp_cc fmt r = pp_print_string fmt (cc_to_string r)
let pp_sse fmt r = pp_print_string fmt (sse_to_string r)
let pp_scale fmt r = pp_print_string fmt (scale_to_string r)



let pp_address fmt addr =
  match (addr.addrDisp = Int64.zero, addr.addrBase, addr.addrIndex, addr.segBase) with
    true, None, None, None -> pp_print_string fmt "[0]"
  | true, Some r, None, None -> fprintf fmt "[%a]" pp_reg32 r
  | true, Some r1, Some (Scale1, r2), None -> fprintf fmt "[%a+%a]" pp_reg32 r1 pp_reg32 r2
  | true, Some r1, Some (sc, r2), None -> fprintf fmt "[%a+%a*%a]" pp_reg32 r1 pp_scale sc pp_reg32 r2
  | true, None, Some (Scale1, r), None -> fprintf fmt "[%a]" pp_reg32 r
  | true, None, Some (sc, r), None -> fprintf fmt "[%a*%a]" pp_scale sc pp_reg32 r
  | false, None, None, None -> fprintf fmt "[%a]" pp_addr addr.addrDisp
  | false, None, None, Some sr -> fprintf fmt "[%a:%a]" pp_segment_reg sr pp_addr addr.addrDisp
  | _ , _ , _  , Some sr -> raise (Print "Unknown segment override displacement")
  | false, Some r, None, None -> fprintf fmt "[%a+%a]" pp_addr addr.addrDisp pp_reg32 r
  | false, Some r1, Some (Scale1, r2), None -> fprintf fmt "[%a+%a+%a]"
	pp_addr addr.addrDisp pp_reg32 r1 pp_reg32 r2
  | false, Some r1, Some (sc, r2), None -> fprintf fmt "[%a+%a+%a*%a]"
	pp_addr addr.addrDisp pp_reg32 r1 pp_scale sc pp_reg32 r2
  | false, None, Some (Scale1, r), None -> fprintf fmt "[%a+%a]" pp_int64 addr.addrDisp pp_reg32 r
  | false, None, Some (sc, r), None -> fprintf fmt "[%a+%a*%a]" pp_int64 addr.addrDisp pp_scale sc pp_reg32 r

let pp_genop pp_reg fmt = function
    Imm n -> pp_int64 fmt n
  | Reg r -> pp_reg fmt r
  | Address addr -> pp_address fmt addr
let pp_op32 = pp_genop pp_reg32
let pp_op8 = pp_genop pp_reg8

let pp_genop_addr pp_reg fmt = function
    Imm n -> pp_addr fmt n
  | Reg r -> pp_reg fmt r
  | Address addr -> pp_address fmt addr
let pp_genop_addr32 = pp_genop_addr pp_reg32
let pp_genop_addr8 = pp_genop_addr pp_reg8

let pp_arith_op fmt aop =
  let s = arith_op_to_string aop in
  pp_print_string fmt s

let pp_shift_op fmt sop =
  let s = shift_op_to_string sop in
  pp_print_string fmt s
  
exception PrintExn of string
  
let pp_instr fmt = function
    Arith (aop, dst, src) -> 
    fprintf fmt "@[@ %a@ %a,@ %a@]" pp_arith_op aop pp_op32 dst pp_op32 src
  | Arithb (aop, dst, src) -> fprintf fmt "@[%aB@ %a,@ %a@]" pp_arith_op aop pp_op8 dst pp_op8 src
  | Call dst -> fprintf fmt "@[ CALL@ %a@]" pp_genop_addr32 dst
  | Cmp (dst, src) -> fprintf fmt "@[@ CMP@ %a,@ %a@]" pp_op32 dst pp_op32 src
  | Test (dst, src) -> fprintf fmt "@[@ TEST@ %a,@ %a@]" pp_op32 dst pp_op32 src
  | Inc gop -> fprintf fmt "@[@ INC@ %a@]" pp_op32 gop
  | Dec gop -> fprintf fmt "@[@ DEC@ %a@]" pp_op32 gop
  | Jcc (cc, imm) -> fprintf fmt "@[@ J%a@ %a@]" pp_cc cc pp_addr imm
  | Jmp dst -> fprintf fmt "@[@ JMP@ %a@]" pp_genop_addr32 dst
  (* | Div src -> fprintf fmt "@[@ DIV@ %a@]" pp_genop_addr32 src *)
  | Lea (dst, src) -> fprintf fmt "@[@ LEA@ %a,@ %a@]" pp_reg32 dst pp_address src
  | Leave -> fprintf fmt "@[ LEAVE@]"
  | Mov (dst, src) -> fprintf fmt "@[@ MOV@ %a,@ %a@]" pp_op32 dst pp_op32 src
  | Movb (dst, src) -> fprintf fmt "@[ MOVB@ %a,@ %a@]" pp_op8 dst pp_op8 src
  | Movzx (dst, src) -> fprintf fmt "@[ MOVZX@ %a,@ %a@]" pp_op32 dst pp_op8 src
  | Exchange (r1, r2) -> fprintf fmt "@[ EXCHG@ %a,@ %a@]" pp_reg32 r1 pp_reg32 r2
  | Pop gop -> fprintf fmt "@[ POP@ %a@]" pp_op32 gop
  | Push gop -> fprintf fmt "@[ PUSH@ %a@]" pp_op32 gop
  | Ret -> fprintf fmt "@[ RET@]"
  | Shift (sop, dst, offset) -> fprintf fmt "@[@ %a@ %a,@ %a@]" pp_shift_op sop pp_op32 dst pp_op8 offset
  | Halt -> fprintf fmt "@[ HALT @]"
  | Skip -> fprintf fmt "@[ SKIP @]"
  | FlagSet (f, v) -> if v then fprintf fmt "@[@ Set %a@]" pp_flag f
                           else fprintf fmt "@[@ Clear %a@]" pp_flag f
  (* | _ -> raise (PrintExn "x86Print: Unsupported instruction") *)

