(*===========================================================================
    X86 Exceptions
  ===========================================================================*)
Require Import String.

Inductive GeneralException :=
| ExnDE  (* Divide error *)
| ExnDB  (* Debug *)
| ExnBP  (* Breakpoint *)
| ExnOF  (* Overflow *)
| ExnBR  (* Bound range *)
| ExnUD  (* Undefined opcode *)
| ExnNM  (* Device not available *)
| ExnDF  (* Double fault *)
| ExnTS  (* Invalid TSS *)
| ExnNP  (* Segment not present *)
| ExnSS  (* Stack Segment fault *)
| ExnGP  (* General Protection *)
| ExnPF  (* Page Fault *)
| ExnMF  (* Floating-point error *)
| ExnAC  (* Alignment check *)
| ExnMC  (* Machine checkl *)
| ExnXM  (* SIMD floating-point numeric error *)
.

Definition exnToString exn :=
  match exn with
  | ExnDE => "#DE: Divide Error"
  | ExnDB => "#DB: RESERVED"
  | ExnBP => "#BP: Breakpoint"
  | ExnOF => "#OF: Overflow"
  | ExnBR => "#BR: BOUND Range Exceeded"
  | ExnUD => "#UD: Invalid Opcode"
  | ExnNM => "#NM: Device Not Available"
  | ExnDF => "#DF: Double Fault"
  | ExnTS => "#TS: Invalid TSS"
  | ExnNP => "#NP: Segment Not Present"
  | ExnSS => "#SS: Stack-Segment Fault"
  | ExnGP => "#GP: General Protection"
  | ExnPF => "#PF: Page Fault"
  | ExnMF => "#MF: x86 FPU Floating Point Error"
  | ExnAC => "#AC: Alignment Check"
  | ExnMC => "#MC: Machine Check"
  | ExnXM => "#XM: SIMD Floating-Point Exception"
  end%string.

