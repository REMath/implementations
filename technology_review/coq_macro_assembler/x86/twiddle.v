(*======================================================================================
  TWIDDLE: 
  A small, first-order, terminating, untyped CPS-based functional language with an easy 
  translation to machine code.

  Key design points:
  * second-class CPS, a la Kennedy, ICFP'07
  * sub-terms of values must be variables (as in ICFP'07)
  * binders are represented using Chlipala's PHOAS, as in his POPL'10 paper
  ======================================================================================*)
Require Import ssreflect ssrbool ssrfun ssrnat tuple seq eqtype.
Require Import bitsrep bitsops instr procstate instrsyntax eval monad enc encinstr.
Require Import SPred septac spec safe basic program macros programassem.
Require Import reader pointsto cursor.
Require Import NaryFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*---------------------------------------------------------------------------
    The language syntax
  ---------------------------------------------------------------------------*)

(* Our primitive operations correspond to those of x86 *)
Inductive PrimBinOp := Add | Sub | And | Or | Xor.
Inductive PrimUnaryOp := Not | Neg.
Inductive PrimCond := Lt | Gt | Eq | Ne | Le | Ge.

(* Indeed, we can translation directly into x86 prim ops *)
Definition PrimBinOpToBinOp op :=
  match op with
  | Add => OP_ADD
  | Sub => OP_SUB
  | And => OP_AND
  | Or => OP_OR
  | Xor => OP_XOR
  end.

Definition PrimUOpToUOp op :=
  match op with
  | Not => OP_NOT
  | Neg => OP_NEG
  end.

(* We represent values using Chlipala's PHOAS, with V standing for the type of variables *)
(* For now, all values are 32-bit integers *)
Inductive PreVal (V: Type) :=
  | VBINOP (op: PrimBinOp) (arg1 arg2: V)
  | VUOP (op: PrimUnaryOp) (arg: V)
  | IMM (c: DWORD)
.
Implicit Arguments IMM [V].

(* Unfortunately we need a well-formedness relation, as in Chlipala, POPL'10 *)
Inductive PreValEq V W (G: V -> W -> Prop) : PreVal V -> PreVal W -> Prop :=
| VBINOP_EQ op v1 v2 w1 w2 : G v1 w1 -> G v2 w2 -> 
                             PreValEq G (VBINOP op v1 v2) (VBINOP op w1 w2)
| VUOP_EQ op v w : G v w -> PreValEq G (VUOP op v) (VUOP op w)
| IMM_EQ c : PreValEq G (IMM c) (IMM c). 

(* For terms, V is again the type of value variables, K n is the type of 
   continuation variables of arity n *)
Inductive PreTm V (K: nat -> Type)  :=
| LET  (v: PreVal V) (e: V -> PreTm V K)
| LETCONT n (block: n.-tuple V -> PreTm V K) (e: K n -> PreTm V K)
| APPCONT n (k: K n) (args: n.-tuple V)
| COND (arg1: V) (cc: PrimCond) (arg2: V) (yes no: PreTm V K)
.

Coercion fromNary V : forall n, V^n -> n.-tuple V :=
  fix fromNaryAux n :=
  if n is n.+1 return V^n -> n.-tuple V 
  then fun xs => cons_tuple xs.1 (fromNaryAux _ xs.2) else fun _ => @nil_tuple _.

Program Definition appContTo V (K: nat -> Type) (args: seq V) k := 
  @APPCONT V K (size args) k (@Tuple (size args) V args _).
Implicit Arguments appContTo [V K]. 

(* A procedure taking n 32-bit arguments and returning one 32-bit result *)
Inductive PreProc n V K :=
| PROC (body: K 1 -> n.-tuple V -> PreTm V K).

(* Closed program, no arguments *)
Definition Program := forall V K, PreProc 0 V K.

(* Now some nice notation. Can almost write C-like syntax! *)
Delimit Scope twiddle_scope with twiddle.

Notation "'var' x = v ';' e" := 
  (LET v (fun x => e)) 
  (right associativity, at level 200, x ident, v, e at level 200) : twiddle_scope.

Notation "'var' x = v '+' w ';' e" := 
  (LET (VBINOP Add v w) (fun x => e)) 
  (right associativity, at level 200, x ident, v, w, e at level 200) : twiddle_scope.

Notation "'const' x = n ';' e" := 
  (LET (IMM #n) (fun x => e)) 
  (right associativity, at level 200, x ident, n at level 1, e at level 200) : twiddle_scope.

Notation "'const' x = '0' 'x' h ';' e" := 
  (LET (IMM (fromHex h)) (fun x => e)) 
  (right associativity, at level 200, x ident, n at level 1, e at level 200) : twiddle_scope.

Notation "'goto' k '(' x ',' y ')'" := 
  (appContTo [::x;y] k) 
  (right associativity, at level 100, k, x at level 1) : twiddle_scope.
  
Notation "'goto' k x" := 
  (appContTo [::x] k) 
  (right associativity, at level 100, k, x at level 1) : twiddle_scope.
  
Notation "'if' '(' x '==' y ')' 'then' e 'else' f" :=
  (COND x Eq y e f) 
  (at level 200, e, f at level 200, x,y at level 1) : twiddle_scope.

Notation "'if' '(' x '!=' y ')' 'then' e 'else' f" :=
  (COND x Ne y e f) 
  (at level 200, e, f at level 200, x,y at level 1) : twiddle_scope.

Notation "'if' '(' x '<' y ')' 'then' e 'else' f" :=
  (COND x Lt y e f) 
  (at level 200, e, f at level 200, x,y at level 1) : twiddle_scope.

Notation "'if' '(' x '>' y ')' 'then' e 'else' f" :=
  (COND x Gt y e f) 
  (at level 200, e, f at level 200, x,y at level 1) : twiddle_scope.

Notation "'if' '(' x '<=' y ')' 'then' e 'else' f" :=
  (COND x Le y e f) 
  (at level 200, e, f at level 200, x,y at level 1) : twiddle_scope.

Notation "'if' '(' x '>=' y ')' 'then' e 'else' f" :=
  (COND x Ge y e f) 
  (at level 200, e, f at level 200, x,y at level 1) : twiddle_scope.

Notation "'proc' '(' k x ')'  e" := (PROC (fun k x => let k := k in e)) 
  (at level 200, k ident, e at level 200) : twiddle_scope. 

Notation "'block' k x 'is' '(' e ')' f" := 
  (LETCONT (fun x => let x := thead x in e) (fun k => let k := k in f)) 
  (at level 200, k ident, x ident, e, f at level 200) : twiddle_scope.

Notation "'block' k '(' x ',' y ')' 'is' '(' e ')' f" := 
  (LETCONT (fun args:2.-tuple _ => let y := thead (behead_tuple args) in let x := thead args in e) (fun k => let k := k in f)) 
  (at level 200, k ident, x ident, e, f at level 200) : twiddle_scope.


(*
Notation "'(' x ')'" := ([tuple x]) : arg_scope.
Delimit Scope arg_scope with arg. 

Notation "k '@' x" := (k x%arg) (at level 80). 
*)

Notation "a + b" := (VBINOP Add a b) : twiddle_scope.
Notation "a - b" := (VBINOP Sub a b) : twiddle_scope.

(* Some examples. *)
Example ex : Program := 
  fun _ _ =>
  (proc(k arg)
  const a = 5;
  const b = 8;
  var c = a+b;
  goto k c)%twiddle. 

Example ex2 : Program :=
  fun _ _ =>
  (proc(k arg)
  const a = 5;
  const b = 8;
  if (a==b)
  then goto k a
  else goto k b)%twiddle.

Example ex4 : Program :=
  fun _ _ =>
  (proc(r arg)
  const a = 5;
  const b = 8;
  block k ( x, y ) is (var c = x+x; goto r c)
  if (a==b)
  then goto k (a,a)
  else goto k (b,b))%twiddle.

Example ex3 : Program :=
  fun _ _ =>
  (proc(k arg) (const a = 5; goto k a))%twiddle.
Close Scope twiddle_scope.

(*---------------------------------------------------------------------------
    The semantics, given by an evaluator
    This is very easy in the PHOAS style
  ---------------------------------------------------------------------------*)

Module Ev.

  (* Result of evaluating a value *)
  Definition VTy := DWORD.

  (* Type of a continuation *)
  Definition KTy n := n.-tuple DWORD -> DWORD.

  Fixpoint evalVal (v: PreVal VTy) := 
  match v with
  | VBINOP Add v w => addB v w
  | VBINOP Sub v w => subB v w
  | VBINOP And v w => andB v w
  | VBINOP Or v w => orB v w
  | VBINOP Xor v w => xorB v w
  | VUOP Not v => invB v 
  | VUOP Neg v => negB v
  | IMM n => n
  end. 

  Fixpoint evalTm (t: PreTm VTy KTy) :=
  match t with
  | APPCONT m k v => k v
  | LETCONT m e f => evalTm (f (fun x => evalTm (e x))) 
  | LET v e     => evalTm (e (evalVal v))
  | COND x Lt y e f => if ltB x y then evalTm e else evalTm f
  | COND x Gt y e f => if ltB y x then evalTm e else evalTm f
  | COND x Le y e f => if leB x y then evalTm e else evalTm f
  | COND x Ge y e f => if leB y x then evalTm e else evalTm f
  | COND x Eq y e f => if x == y then evalTm e else evalTm f
  | COND x Ne y e f => if x != y then evalTm e else evalTm f
  end.

  Definition evalProc {n} (p: PreProc n VTy KTy) :=
  match p with
  | PROC e => fun ys => evalTm (e (fun xs => thead xs) ys)
  end.

Check evalProc.
  Definition evalProgram (p: Program) :=
  evalProc (p _ _) [tuple]. 


  (* We can execute programs inside Coq, as long as we convert to a nice type *)
  Compute toNat (evalProgram ex). 

  (* Or we can do trivial proofs by computation *)
  Lemma exIsFive : evalProgram ex = #13. 
  Proof. by apply val_inj. Qed. 
End Ev.

(*---------------------------------------------------------------------------
    Alternative environment-based semantics, instantiating VTy to nat
  ---------------------------------------------------------------------------*)

Module EnvEv.

  (* Level of variable *)
  Definition VTy := nat.

  (* Type of a continuation *)
  Definition KTy n := n.-tuple DWORD -> DWORD.

  Definition evalVar (env: seq DWORD) (v: VTy) := List.nth (List.length env - v - 1) env #0.

  Definition evalVal env (v: PreVal VTy) := 
  match v with
  | VBINOP Add v w => addB (evalVar env v) (evalVar env w)
  | VBINOP Sub v w => subB (evalVar env v) (evalVar env w)
  | VBINOP And v w => andB (evalVar env v) (evalVar env w)
  | VBINOP Or v w => orB (evalVar env v) (evalVar env w)
  | VBINOP Xor v w => xorB (evalVar env v) (evalVar env w)
  | VUOP Not v => invB (evalVar env v)
  | VUOP Neg v => negB (evalVar env v)
  | IMM n => n
  end. 

  Fixpoint evalTm env (t: PreTm VTy KTy) :=
  match t with
  | LET v e => evalTm (evalVal env v :: env) (e (List.length env))
  | COND x Lt y e f => if ltB (evalVar env x) (evalVar env y) then evalTm env e else evalTm env f
  | COND x Gt y e f => if ltB (evalVar env y) (evalVar env x) then evalTm env e else evalTm env f
  | COND x Le y e f => if leB (evalVar env x) (evalVar env y) then evalTm env e else evalTm env f
  | COND x Ge y e f => if leB (evalVar env y) (evalVar env x) then evalTm env e else evalTm env f
  | COND x Eq y e f => if evalVar env x == evalVar env y then evalTm env e else evalTm env f
  | COND x Ne y e f => if evalVar env x != evalVar env y then evalTm env e else evalTm env f
  | APPCONT m k v => k (map_tuple (evalVar env) v)
  | LETCONT m e f => evalTm env (f (fun x => evalTm env (e (iota_tuple m (List.length env)))))
  end.

  Definition evalProc {n} (p: PreProc n VTy KTy) :=
  match p with
  | PROC e => fun args: seq DWORD => evalTm args (e (fun xs => thead xs) (iota_tuple n 0))
  end.

  Definition evalProgram (p: Program) :=
  evalProc (p _ _) [tuple]. 

  (* We can execute programs inside Coq, as long as we convert to a nice type *)
  Compute toNat (evalProgram ex). 

  (* Or we can do trivial proofs by computation *)
  Lemma exIsFive : evalProgram ex = #13. 
  Proof. by apply val_inj. Qed. 
End EnvEv.


(*---------------------------------------------------------------------------
    Non-optimizing compilation to machine code
  ---------------------------------------------------------------------------*)
Module Compile.

  (* Result of compiling a value *)
  Definition VTy := InstrArg.

  (* Type of a continuation: its address, and level *)
  Definition KTy (n:nat) := (DWORD * nat)%type.


  Open Scope instr_scope.

  Definition compileVar (v: nat) : MemSpec :=
    [EBP + (4*v)]. 

  Fixpoint compileVal dst (v: PreVal nat) := 
  match v with
  | VBINOP Add v w => MOV EAX, compileVar v;; ADD EAX, compileVar w;; MOV dst, EAX
  | VBINOP Sub v w => MOV EAX, compileVar v;; SUB EAX, compileVar w;; MOV dst, EAX
  | VBINOP And v w => MOV EAX, compileVar v;; AND EAX, compileVar w;; MOV dst, EAX
  | VBINOP Or  v w => MOV EAX, compileVar v;; OR EAX, compileVar w;; MOV dst, EAX
  | VBINOP Xor v w => MOV EAX, compileVar v;; XOR EAX, compileVar w;; MOV dst, EAX
  | VUOP Not v => MOV EAX, compileVar v;; MOV dst, EAX;; makeUOP OP_NOT dst
  | VUOP Neg v => MOV EAX, compileVar v;; MOV dst, EAX;; makeUOP OP_NEG dst
  | IMM n => MOV dst, n
  end. 

  Fixpoint localsP l ebp (env: seq DWORD) :=
  if env is v::env then ebp +# 4*l :-> v ** localsP l.-1 ebp env 
  else empSP.
  
  Require Import septac spectac instrrules.

  Lemma compileVarCorrect l env (v:nat) ebp :
    EBP ~= ebp ** localsP l ebp env |-- EBP ~= ebp ** localsP l ebp env /\\ EnvEv.evalVar v env = 
  Lemma compileValCorrect l dst env (v:PreVal nat) :
    |-- Forall ebp: DWORD, 
    basic (ebp +# 4*dst :-> ?:DWORD) (compileVal [EBP + (dst*4)] v)
          (ebp +# 4*dst :-> EnvEv.evalVal  env v) @ 
          (EAX? ** EBP ~= ebp ** localsP l ebp env).
  Proof. 
  induction v; rewrite /compileVal-/compileVal/compileVar/EnvEv.evalVal-/EnvEv.evalVal. 
  + destruct op. 
    specintro => ebp. autorewrite with push_at. 
    basicapply MOV_RM_rule. ; last first.
    basicapply ADD_RM_rule. ssimpl. 
    
  Fixpoint setArgs l m : (m.-tuple nat) -> program :=
  if m is m.+1 
  then fun vs => MOV EAX, compileVar (thead vs);; MOV [EBP + (4*l)], EAX;; setArgs l.+1 (behead_tuple vs)
  else fun vs => prog_skip.

(*
  Fixpoint makeParams l m : m.-tuple nat :=
  if m is m.+1 then cons_tuple (MemSpecArg (mkMemSpec EBP None #((l+m)*4))) (makeParams l m) else nil_tuple _.
*)

  (* Compile a term. Must end with a jump or return *)
  Fixpoint compileTm l (t: PreTm VTy KTy) :=
  match t with
  | APPCONT m k v => 
    setArgs k.2 v;; 
    JMP (mkTgt k.1)

  | LET v e     => 
    compileVal [EBP + (4*l)] v;; 
    compileTm l.+1 (e [EBP + (4*l)])

  | COND x c y e1 e2 => 
    let f := match c with
    | Gt => ifthenelse CC_LE false
    | Le => ifthenelse CC_LE true
    | Ge => ifthenelse CC_L false
    | Lt => ifthenelse CC_L true
    | Eq => ifthenelse CC_Z true
    | Ne => ifthenelse CC_Z false
    end 
    in MOV EAX, x;; CMP EAX, y;; f (compileTm l e1) (compileTm l e2)

  | LETCONT m e1 e2 => 
    LOCAL CONT; 
      compileTm l (e2 (CONT,l));; 
    CONT:;; 
      compileTm (m+l) (e1 (makeParams l m))
  end.

  Definition compileProc {n} (p: PreProc n VTy KTy) :=
  match p with
  | PROC e => LOCAL FINISH; compileTm n.+1 (e (FINISH,0) (makeParams 0 n));; FINISH:;; MOV EAX, [EBP+0];; RET 0 
  end.

  Definition compileProgram (p: Program) :=
  compileProc (p _ _). 

  Eval showinstr in linearize (compileProgram ex).

Check ex.
Print Program. Check compileVal. Check Ev.evalVal.
Check Ev.evalVal.

Module Correctness.

  Check Definition 

  Require Import programassem.
  Definition bytes := 
    assemble #x"C0000004" (Compile.compileProgram ex2).
  Compute bytesToHex bytes. 

End Compile.
