(*===========================================================================
  Macros for defining and calling functions using x86 calling conventions
  used by C compilers.
  ===========================================================================*)
Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq fintype tuple.
Require Import procstate procstatemonad bitsrep bitsops bitsprops bitsopsprops.
Require Import SPred septac spec safe basic program macros call.
Require Import instr instrsyntax.
Require Import NaryFunctions.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope instr_scope.

(*---------------------------------------------------------------------------
    Calling-convention-independent definitions
  ---------------------------------------------------------------------------*)

(* A function signature is simply an arity and a bool 
   denoting the presence or absence of a return value. In future we could 
   extend this to deal with other types e.g. floats, 64-bit integers *)
Structure FunSig := mkFunSig { arity: nat; nonvoid: bool }.

(* A function body can be defined independently of calling convention by
   parameterizing it on InstrSrc arguments. Result is assumed to be in EAX. *)
Definition programWithSig sig := 
  InstrSrc ^^ arity sig --> program.

(* Here is an example: \n.n+1 *)
Example incBody : programWithSig (mkFunSig 1 true) :=
  fun arg => makeMOV EAX arg;; INC EAX.

(*---------------------------------------------------------------------------
    Helpers for calling
  ---------------------------------------------------------------------------*)

(* Push n arguments on the stack *)
Fixpoint pushArgs n (p:program) : nfun Src n program := 
  if n is n.+1
  then fun arg => pushArgs n (PUSH arg;; p) 
  else p.

Definition makeMOVsrc (r:Reg) (s: Src) : program :=
  match s with
  | SrcI c => MOV r, c
  | SrcM m => MOV r, m
  | SrcR r' => if r==r' then prog_skip else MOV r, r'
  end.

(* Put first argument in ECX, second in EDX, and the rest on the stack *)
Definition pushFastArgs n (p:program) : nfun Src n program := 
  match n with
  | 0 => p
  | 1 => fun arg => (makeMOVsrc ECX arg;; p)
  | n.+2 => fun arg1 arg2 => pushArgs n (makeMOVsrc ECX arg1;; makeMOVsrc EDX arg2;; p) 
  end.

(*---------------------------------------------------------------------------
    We support three x86 calling conventions:
    * cdecl
      - arguments pushed right to left
      - result (if any) in EAX
      - EAX, ECX, EDX are caller-saved, rest callee-saved
      - caller cleans up stack (typically using ADD ESP, n)
    * stdcall
      - arguments pushed right to left
      - result (if any) in EAX
      - EAX, ECX, EDX are caller-saved, rest callee-saved
      - callee cleans up stack (typically using RET n)
    * fastcall
      - first argument passed in ECX, second in EDX, remainder pushed right to left
      - result (if any) in EAX
      - EAX, ECX, EDX are caller-saved, rest callee-saved
      - callee cleans up stack (typically using RET n)
  ---------------------------------------------------------------------------*)

(*=CallConv *)
Inductive CallConv := cdecl | stdcall | fastcall.
(*=End *)

(*---------------------------------------------------------------------------
    Generate calling sequence for cdecl, stdcall and fastcall conventions 
  ---------------------------------------------------------------------------*)
Definition call_cdecl_with (n:nat) (f:JmpTgt) := 
  pushArgs n (CALL f;; ADD ESP, n*4).

Definition call_std_with (n:nat) (f: JmpTgt) :=
  pushArgs n (CALL f).

Definition call_fast_with (n:nat) (f: JmpTgt) :=
  pushFastArgs n (CALL f).

Definition call_with (cc: CallConv) :=
  match cc with
  | cdecl => call_cdecl_with
  | stdcall => call_std_with
  | fastcall => call_fast_with
  end.

 
(*---------------------------------------------------------------------------
    Helper for creating function prologues and epilogues
  ---------------------------------------------------------------------------*)
Fixpoint introParams n offset : InstrSrc ^^ n --> program -> program :=
  if n is n'.+1
  then fun p => introParams (offset + 4) (p [EBP + offset])
  else fun p => p.
Implicit Arguments introParams [].


(*---------------------------------------------------------------------------
    Create function definitions for cdecl, stdcall and fastcall conventions 
  ---------------------------------------------------------------------------*)
Definition def_cdecl sig : programWithSig sig -> program :=
  match sig return programWithSig sig -> program with
  | mkFunSig n _ => 
    fun body => 
    PUSH EBP;; MOV EBP, ESP;; 
    introParams n 8 body;; POP EBP;; RET 0
  end.
Implicit Arguments def_cdecl [].

Definition def_std sig : programWithSig sig -> program :=
  match sig return programWithSig sig -> program with
  | mkFunSig n _ => 
    fun body => 
    PUSH EBP;; MOV EBP, ESP;; 
    introParams n 8 body;; POP EBP;; RET (n*4)

  end.
Implicit Arguments def_std [].

Definition def_fast sig := 
  match sig return programWithSig sig -> program with
  | mkFunSig 0 _ => fun body => body;; RET 0
  | mkFunSig 1 _ => fun body => body ECX;; RET 0
  | mkFunSig 2 _ => fun body => body ECX EDX;; RET 0
  | mkFunSig n.+2 _ => 
    fun body => PUSH EBP;; MOV EBP, ESP;; introParams n 8 (body ECX EDX);; POP EBP;; RET 0
  end.
Implicit Arguments def_fast [].

Definition def_fun cc :=
  match cc with
  | cdecl => def_cdecl
  | stdcall => def_std
  | fastcall => def_fast
  end.
Implicit Arguments def_fun [].

Definition callconv cc sig := (call_with cc sig.(arity), def_fun cc sig).

(* Examples: compare http://en.wikibooks.org/wiki/X86_Disassembly/Calling_Conventions *)
      
(*=addfun *)
Example addfun (cc: CallConv) := 
  let (call, def) := callconv cc (mkFunSig 3 true) in
  LOCAL MyFunc;
  MyFunc:;; def (fun arg1 arg2 arg3 =>
    MOV EAX, arg1;; 
    ADD EAX, arg2;;
    ADD EAX, arg3);;
  call MyFunc 2 3 4.
(*=End *)

Eval showinstr in linearize (addfun cdecl). 
Eval showinstr in linearize (addfun stdcall). 
Eval showinstr in linearize (addfun fastcall). 

