(* Known "bugs":  multiplying two int64s does not work (throws an exception in
   IRUtil.typereg_of_int because it tries to create a TypeReg_ term for a 
   128-bit quantity, which does not exist within the IR). However, this is not
   supported in the IR anyway, and typechecking ought to prevent this. *)
(* To do:  Binop(_,ULT|ULE|SLT|SLE,_) *)
open IR

exception BitwiseAIExn of string

let failwith s = raise (BitwiseAIExn(s))

(* A bit is either known to be zero or one, or it is unknown (half) *)
type abstract_bit =
| AbsZero
| AbsOne
| AbsHalf

(* Debugging functions *)
let string_of_abstract_bit = function
| AbsZero -> "0"
| AbsOne  -> "1"
| AbsHalf -> "1/2"

let string_of_abstract_bitvector arr = 
  let len = Array.length arr in
  let descr = Array.fold_left (fun acc a -> string_of_abstract_bit a^" "^acc) "" arr in
  "BV("^string_of_int len^"): "^descr

(* This data type mimics a variable in the main IR definition; it's either a
   bitvector term or a memory. *)
type absvalue = 
| AbsValue of abstract_bit array 
| AbsMem of (int64 -> abstract_bit array)

(* Convert an abstract bit into an integer, so we can index them into tables *)
let int_of_abstract_bit = function
| AbsZero -> 0
| AbsOne  -> 2
| AbsHalf -> 1

(* Create a bitvector of size IRUtil.bits s based on the contents of a 
   Const(i,s) *)
let abstract_bv_of_constant i s =
  let make_mask i = Int64.shift_left Int64.one i in
  let se = IRUtil.bits s in
  let arr = Array.make se (AbsZero) in
  for j = 0 to (se-1) do
    let store = 
      match (Int64.logand i (make_mask j) <> Int64.zero) with
      | true  -> AbsOne
      | false -> AbsZero
    in arr.(j) <- store 
  done;
  arr

(* Partially applied wrapper function for abstract bitwise binops.  Returns
   a function that expects two equally-sized abstract bitvectors. *)
let abstract_bitwise_op table = 
  ArrayUtil.map2 
    (AbsZero) 
    (fun x y -> table.(int_of_abstract_bit x).(int_of_abstract_bit y)) 

(* Abstract version of xor.  Works like you'd expect. *)
let abstract_xor_table = 

            (* 0 *)  (*1/2*)  (* 1 *)
(* 0 *)[|[| AbsZero; AbsHalf; AbsOne  |];
(*1/2*)  [| AbsHalf; AbsHalf; AbsHalf |];
(* 1 *)  [| AbsOne;  AbsHalf; AbsZero |]|]

let abstract_xor = abstract_bitwise_op abstract_xor_table

(* Abstract version of or.  Works like you'd expect. *)
let abstract_or_table = 

            (* 0 *)  (*1/2*)  (* 1 *)
(* 0 *)[|[| AbsZero; AbsHalf; AbsOne  |];
(*1/2*)  [| AbsHalf; AbsHalf; AbsOne  |];
(* 1 *)  [| AbsOne;  AbsOne ; AbsOne  |]|]

let abstract_or = abstract_bitwise_op abstract_or_table

(* Abstract version of and.  Works like you'd expect. *)
let abstract_and_table = 

            (* 0 *)  (*1/2*)  (* 1 *)
(* 0 *)[|[| AbsZero; AbsZero; AbsZero |];
(*1/2*)  [| AbsZero; AbsHalf; AbsHalf |];
(* 1 *)  [| AbsZero; AbsHalf; AbsOne  |]|]

let abstract_and = abstract_bitwise_op abstract_and_table

(* Abstract version of not.  Works like you'd expect. *)
let abstract_not_table =
   (* 0 *)  (*1/2*)  (* 1 *)
[| AbsOne ; AbsHalf; AbsZero |]

let abstract_not = Array.map (fun i -> abstract_not_table.(int_of_abstract_bit i))

(* Common function used in abstract shift operators. *)
let abstract_shift init f lhs_arr i =
  let len = Array.length lhs_arr in
  let newarr = Array.make len init in
  for j = 0 to ((len - i) - 1) do f newarr lhs_arr j i done;
  newarr

(* Abstract versions of shift left/right/arithmetic right. *)
let abstract_shl =
  let shl newarr lhs_arr j i =
    let len = Array.length lhs_arr in
    newarr.((len-1)-j) <- lhs_arr.((len-1) - (j+i))
  in abstract_shift (AbsZero) shl
 
let shr newarr lhs_arr j i = newarr.(j) <- lhs_arr.(i+j)
let abstract_shr = abstract_shift (AbsZero) shr
let abstract_sar lhs_arr i = abstract_shift (lhs_arr.(Array.length lhs_arr-1)) shr lhs_arr i

(* Abstract addition and subtraction.  Addition works with the notion of an 
   "abstract carry flag"; for example, if two corresponding bits are 0 and 1, 
   respectively, and the abstract carry flag is 1/2, then:
   if the abstract carry flag is 0, we get (1,0)
   if the abstract carry flag is 1, we get (0,1)
   Therefore both the result and the abstract carry flag are variable, so
   the return value is (1/2,1/2).  Apply this process sequentially over the
   entirety of the bitvectors. 
   
   Subtraction is defined as being the same thing as addition, with the RHS
   NOT-ted, and the initial carry flag being set to one instead of zero.  This
   comes from Digital Design:  Principles and Practices, Third Edition, by 
   John F. Wakerly.  Testing indicates that it works for non-half bits. *)
let abstract_add_or_sub initial_carry f_rhs lhs_arr rhs_arr =
  let abstract_add_bits ab1 ab2 abc =
    match ab1,ab2,abc with
    | AbsZero, AbsZero, AbsZero -> (AbsZero,AbsZero)
    | AbsZero, AbsZero, AbsOne  -> (AbsOne,AbsZero)
    | AbsZero, AbsZero, AbsHalf -> (AbsHalf,AbsZero)
    | AbsZero, AbsOne,  AbsZero -> (AbsOne,AbsZero)
    | AbsZero, AbsOne,  AbsOne  -> (AbsZero,AbsOne)
    | AbsZero, AbsOne,  AbsHalf -> (AbsHalf,AbsHalf)
    | AbsZero, AbsHalf, AbsZero -> (AbsHalf,AbsZero)
    | AbsZero, AbsHalf, AbsOne  -> (AbsHalf,AbsHalf)
    | AbsZero, AbsHalf, AbsHalf -> (AbsHalf,AbsHalf)
    | AbsOne,  AbsZero, AbsZero -> (AbsOne,AbsZero)
    | AbsOne,  AbsZero, AbsOne  -> (AbsZero,AbsOne)
    | AbsOne,  AbsZero, AbsHalf -> (AbsHalf,AbsHalf)
    | AbsOne,  AbsOne,  AbsZero -> (AbsZero,AbsOne)
    | AbsOne,  AbsOne,  AbsOne  -> (AbsOne,AbsOne)
    | AbsOne,  AbsOne,  AbsHalf -> (AbsHalf,AbsOne)
    | AbsOne,  AbsHalf, AbsZero -> (AbsHalf,AbsHalf)
    | AbsOne,  AbsHalf, AbsOne  -> (AbsHalf,AbsOne)
    | AbsOne,  AbsHalf, AbsHalf -> (AbsHalf,AbsHalf)
    | AbsHalf, AbsZero, AbsZero -> (AbsHalf,AbsZero)
    | AbsHalf, AbsZero, AbsOne  -> (AbsHalf,AbsHalf)
    | AbsHalf, AbsZero, AbsHalf -> (AbsHalf,AbsHalf)
    | AbsHalf, AbsOne,  AbsZero -> (AbsHalf,AbsHalf)
    | AbsHalf, AbsOne,  AbsOne  -> (AbsHalf,AbsOne)
    | AbsHalf, AbsOne,  AbsHalf -> (AbsHalf,AbsHalf)
    | AbsHalf, AbsHalf, AbsZero -> (AbsHalf,AbsHalf)
    | AbsHalf, AbsHalf, AbsOne  -> (AbsHalf,AbsHalf)
    | AbsHalf, AbsHalf, AbsHalf -> (AbsHalf,AbsHalf)
  in
  let rhs_arr = f_rhs rhs_arr in
  let lhs_size,rhs_size = Array.length lhs_arr,Array.length lhs_arr in
  if lhs_size <> rhs_size then failwith "typechecking prevents this jlkasglkj";
  
  let out_arr = Array.make lhs_size (AbsZero) in
  let rec aux j c =
    if j < lhs_size 
    then
     (let ar,ac = abstract_add_bits lhs_arr.(j) rhs_arr.(j) c in
      out_arr.(j) <- ar;
      aux (j+1) ac)
  in aux 0 initial_carry;
  out_arr

let abstract_add = abstract_add_or_sub (AbsZero) (fun x -> x)
let abstract_sub = abstract_add_or_sub (AbsOne)  abstract_not

(* Used in multiplication.  A multiplication can be expressed as a series
   of additions of shifted values.  If the corresponding bit in the RHS of
   the mul is a zero, we add a partial product of zeroes.  If the corresponding
   bit in the RHS is one, we add a partial product of the original LHS term
   widened to twice its size and shifted left by the weight of the one bit.
   If the bit is half, then we need to turn every one in the partial product
   into a half (since they will be either 1 or 0), and leave the zero bits 
   alone (since they will always be 0). *)
let replace_ones_with_halves lhs_arr =
  let len = Array.length lhs_arr in
  let newarr = Array.make len (AbsZero) in
  for j = 0 to (len-1) do 
    let old = lhs_arr.(j) in
    newarr.(j) <- match old with
    | AbsZero | AbsHalf -> old
    | AbsOne -> AbsHalf
  done;
  newarr

(* Shift a value into a larger quantity; equivalent to abstract interpreting
   Binop(Cast(Unsigned,size,lhs),Shl,i).  Used in multiplication. *)
let abstract_widening_shl size lhs_arr i =
  let len = Array.length lhs_arr in
  let newarr = Array.make size (AbsZero) in
  for j = 0 to len-1 do newarr.(j+i) <- lhs_arr.(j) done;
  newarr

let abstract_umul lhs_arr rhs_arr = 
  let lhs_size,rhs_size = Array.length lhs_arr,Array.length rhs_arr in
  if lhs_size<>rhs_size then failwith "typechecking prevents this jklasgjlk";
  let out_size = lhs_size * 2 in
  let rec aux j out_arr = 
    if j < lhs_size then
     (match rhs_arr.(j) with
      | AbsZero -> aux (j+1) out_arr
      | AbsOne  -> aux (j+1) (abstract_add out_arr (abstract_widening_shl out_size lhs_arr j))
      | AbsHalf -> aux (j+1) (abstract_add out_arr (replace_ones_with_halves (abstract_widening_shl out_size lhs_arr j))))
    else out_arr
  in aux 0 (Array.make out_size (AbsZero))

(* Abstract EQ/NE operators.  If two corresponding bits differ, then in
   the EQ case, the whole bitvectors can not match (so we return AbsZero), 
   and in the NE case, they definitely are not equal (so we return AbsOne). 
   If the bitvectors are non-half and identical, for EQ we return AbsOne, 
   and for NE we return AbsZero.  If any bits are half, and the first rule
   above does not apply, then we cannot make the determination and so we 
   return AbsHalf. *)
let abstract_equality_compare mismatch final a1 a2 =
  let lhs_size = Array.length a1 in
  let rhs_size = Array.length a2 in
  if lhs_size <> rhs_size then failwith ("typechecking prevents this njmaslgnjk "^string_of_int lhs_size^" "^string_of_int rhs_size);
  let not_constant = ref false in
  let rec aux j =
    if j < lhs_size 
    then
   (match a1.(j),a2.(j) with
    | AbsHalf,_ | _,AbsHalf -> not_constant := true; aux (j+1)
    | AbsOne,AbsZero | AbsZero,AbsOne -> mismatch
    | _ -> aux (j+1))
    else
      if !not_constant then AbsHalf else final
  in ([|aux 0|])
  
let abstract_eq = abstract_equality_compare (AbsZero) (AbsOne)
let abstract_ne = abstract_equality_compare (AbsOne)  (AbsZero)

(* Neg(x) is the same thing as (~x)+1, so we implement this operation in terms 
   of those operations. *)
let abstract_neg a = 
  let ares = abstract_not a in
  abstract_add ares (abstract_bv_of_constant 1L (IRUtil.typereg_of_int (Array.length ares)))

(* Make a bitvector of the proscribed size with all half bits. *)
let make_top s = Array.make (IRUtil.bits s) (AbsHalf)

(* Since the abstract interpreter passes around absvalue terms, it becomes
   cumbersome to continually pattern match over them, extract the innards of
   the AbsValues, perform operations, and then wrap the result in an AbsValue
   constructor again.  Therefore, we abstract this functionality out into this
   little function... *)
let value_wrapped_abstract_binop f v1 v2 = match (v1,v2) with
| AbsValue(v1), AbsValue(v2) -> AbsValue(f v1 v2)
| _,_ -> failwith "typechecking prevents this nmaSMFG" 

(* ... which we then partially apply abstract operators against. *)
let abstract_and  = value_wrapped_abstract_binop abstract_and
let abstract_xor  = value_wrapped_abstract_binop abstract_xor
let abstract_or   = value_wrapped_abstract_binop abstract_or
let abstract_add  = value_wrapped_abstract_binop abstract_add
let abstract_sub  = value_wrapped_abstract_binop abstract_sub
let abstract_umul = value_wrapped_abstract_binop abstract_umul
let abstract_eq   = value_wrapped_abstract_binop abstract_eq
let abstract_ne   = value_wrapped_abstract_binop abstract_ne

(* Same deal, but for shift operators instead of binary ones. *)
let value_wrapped_abstract_shift f v1 i = match v1 with
| AbsValue(v1) -> AbsValue(f v1 i)
| _ -> failwith "typechecking prevents this kljasdlgkj"

let abstract_shl = value_wrapped_abstract_shift abstract_shl
let abstract_shr = value_wrapped_abstract_shift abstract_shr
let abstract_sar = value_wrapped_abstract_shift abstract_sar

(* Same deal, except for unary operators. *)
let value_wrapped_abstract_unop f v1 = match v1 with
| AbsValue(v1) -> AbsValue(f v1)
| _ -> failwith "typechecking prevents this kljasjklf"

let abstract_not = value_wrapped_abstract_unop abstract_not
let abstract_neg = value_wrapped_abstract_unop abstract_neg

(* More sugar for respectively extracting abstract_bit arrays and memories 
   from absvalue terms. *)
let unwrap_abstract_value = function
| AbsValue(v1) -> v1
| _ -> failwith "typechecking prevents this lnmaslnkmg"

let unwrap_abstract_memory = function
| AbsMem(f) -> f
| _ -> failwith "typechecking prevents this jklDGJKL"

(* Take an abstract_bit array and turn it into a constant, if possible.  Return
   an option type with the constant inside of it, or None. *)
let make_constant_opt bv =
  let size = Array.length bv in
  let s = IRUtil.typereg_of_int size in
  let rec aux c j = 
    if j < size 
    then
      match c with 
      | None -> c
      | Some(c) ->
        let res =
         (let bit_opt = 
          match bv.(j) with
          | AbsOne  -> Some(1L)
          | AbsZero -> Some(0L)
          | AbsHalf -> None
          in
          match bit_opt with
          | Some(i) -> Some(Int64.logor c (Int64.shift_left i j))
          | None -> None)
        in aux res (j+1)
    else c
  in 
  match (aux (Some(Int64.zero)) 0) with
  | Some(c) -> Some(Const(c,s))
  | None -> None
   
(* We model memory as a function that takes a non-symbolic, int64 address and 
   returns the 8-bit contents of what's stored there.  Loads against addresses 
   that have not yet been written to return all half bits.  Also, there are two 
   convenience functions for performing loads and stores. *)
let default_abstract_memory = (fun _ -> make_top TypeReg_8)
let abstract_load v mem = mem v
let abstract_store v addr mem = (fun a -> if a = addr then v else mem a)

(* Given an IR var type (memory or variable), return the default abstract value
   (i.e., top for the given size, or an empty memory). *)
let default_abstract_value = function
| Mem(_,_,_) -> AbsMem(default_abstract_memory)
| Variable(_,s) -> AbsValue(make_top s)

(* Use this hashtable to store abstract variable bindings, i.e. v from
   Assign(v,_) instructions and Let(v,_,_) expressions.  Also, convenience
   functions for fetching and storing bindings. *)
let varctx = Hashtbl.create 50
let lookup_varctx v = try Hashtbl.find varctx v with Not_found -> default_abstract_value v
let assign_varctx v e = Hashtbl.add varctx v e

(* This is where all the action is.  This function takes an expression, and 
   returns a pair of (its abstract evaluation, its transformed concrete 
   representation).  As an example of the latter, suppose that as a result of
   the abstract interpretation, we discover that some subexpression is constant.
   We therefore replace the entire subexpression with that constant.  *)
let rec bitwise_abstract_interpret expr = match expr with
| Binop(e1,((And|Or|Xor|Add|Sub|Mul|EQ|NE) as o) ,e2) -> 
  let (a1,te1) = bitwise_abstract_interpret e1 in
  let (a2,te2) = bitwise_abstract_interpret e2 in
  let ares =
    match o with
    | And  -> abstract_and  a1 a2
    | Or   -> abstract_or   a1 a2
    | Xor  -> abstract_xor  a1 a2
    | Add  -> abstract_add  a1 a2
    | Sub  -> abstract_sub  a1 a2
    | Mul  -> abstract_umul a1 a2
    | EQ   -> abstract_eq   a1 a2
    | NE   -> abstract_ne   a1 a2
    | _    -> failwith "impossible"
  in 
  (* If the abstract result of the binop is a constant, replace the whole binop
     with the constant.  Otherwise, return a binop where the left and right 
     subtrees may be simplified. *)
  let cres = match (make_constant_opt (unwrap_abstract_value ares)) with
    | Some(c) -> c
    | None -> Binop(te1, o, te2)
  in (ares,cres)

(* Handle shifts with constant values.  Revisit this for non-constant values? *)
| Binop(e1,((Shl|Shr|Sar) as o),(Const(i,s) as c)) ->
  let (a1,te1) = bitwise_abstract_interpret e1 in
  let i = Int64.to_int i in
  let ares =
    match o with
    | Shl -> abstract_shl a1 i
    | Shr -> abstract_shr a1 i
    | Sar -> abstract_sar a1 i
    | _   -> failwith "impossible"
  in 
  (* Replace binop with constant, if applicable, or replace LHS of binop with
     a possibly transformed expression. *)
  let cres = match (make_constant_opt (unwrap_abstract_value ares)) with
  | Some(c) -> c
  | None -> Binop(te1, o, c)
  in (ares,cres)

(* Handle shifts with "partially constant" values:  e.g. consider
   mov cl, 5
   shr eax, cl
   This gets broken down in the IR to a partially constant assignment into e.g.
   ECX = (ECX & 0xFFFFFF00) | cast(Unsigned,TypeReg_32,const(TypeReg_32,5)), then
   EAX = Binop(EAX,Shr,cast(Low,TypeReg_8,ECX))
   Therefore, ECX itself is not necessarily constant, even though the bottom 8
   bits are.  By abstract interpreting the right-hand side of the binop, we 
   can propagate the 5 into the shift, which then allows it to be handled by 
   the above case.  This type of "partial constant propagation" is not limited
   to shifts, and is in general a major positive point for this abstract 
   interpretation over this IR. *)
| Binop(e1,((Shl|Shr|Sar) as o),e2) ->
  let (a2,te2) = bitwise_abstract_interpret e2 in
 (match te2 with
  | Const(_,_) -> bitwise_abstract_interpret (Binop(e1,o,te2))
  | _ -> (AbsValue(make_top (IRTypeCheck.type_of_integer_type (IRTypeCheck.typecheck_expr e1))),Binop(e1,o,te2)))

(* Do this better.  For now, we only do comparisons if they are constants. *)
| Binop(e1,((ULT|ULE|SLT|SLE) as o),e2) ->
  let (a1,te1) = bitwise_abstract_interpret e1 in
  let (a2,te2) = bitwise_abstract_interpret e2 in
  let cres = Binop(te1,o,te2) in
  let ares = match (te1,te2) with
  | Const(i1,s1),Const(i2,s2) -> 
    let c = IRLocalOpt.fold_expr_constants cres in
   (match c with
    | Const(i,s) -> AbsValue(abstract_bv_of_constant i s)
    | _ -> failwith "impossible uioqwaqwy")
  | _ -> AbsValue([|AbsHalf|])
  in (ares,cres)
  

(* Punt on all binops except the above.  Revisit for the other conditional 
   comparisons.  Should we do anything about shifts by non-constants, and/or 
   division/modulus? *)
| Binop(e1,o,e2) ->
  let _,te1 = bitwise_abstract_interpret e1 in
  let _,te2 = bitwise_abstract_interpret e2 in
  (AbsValue(make_top (IRTypeCheck.type_of_integer_type (IRTypeCheck.typecheck_expr expr))),Binop(te1,o,te2))

(* Handle all unary operations the same way as we handled binops above. *)
| Unop(o,e) -> 
  let (a,te) = bitwise_abstract_interpret e in
  let ares =
    match o with
    | Not -> abstract_not a
    | Neg -> abstract_neg a
  in 
  let cres = match (make_constant_opt (unwrap_abstract_value ares)) with
  | Some(c) -> c
  | None -> Unop(o,te)
  in (ares,cres)

(* Stores and loads are pretty hairy.  We ignore all loads and stores from 
   addresses that are not constant values. *)
| Store(m,a,_,s)
| Load(m,a,s) -> 
  (* Abstract interpret the address we load/store against. *)
  let aa,ta = bitwise_abstract_interpret a in
  (* Fetch the memory we load/store against. *)
  let am,tm = bitwise_abstract_interpret m in
  let am = unwrap_abstract_memory am in
  (* Was the address constant? *)
 (match ta with
  (* Address was constant; try to read from it *)
  | Const(ca,_) when List.mem X86ToIRUtil.vEsp (IRLocalOpt.extract_uses a) -> 
   (match expr with
    | Store(_,_,t,_) -> 
      let at,et = bitwise_abstract_interpret t in
      (* Create a list of (address,abstract_bit array) pairs. *)
      (* Could make this tail-recursive, but who cares *)
      let make_normalized_store_pairs a s =
        let s = (IRUtil.bits s) lsr 3 in
        if s = 0 then failwith "1-bit store";
        let at = unwrap_abstract_value at in
      (*IDA.msg "s: %d length: %d\n" s (Array.length at);*)
        let rec aux i =
          if i < s
          then (Int64.add a (Int64.of_int i), Array.sub at (i*8) 8)::(aux (i+1))
          else []
        in aux 0
      in
      let store_pairs = make_normalized_store_pairs ca s in
    (*List.iter 
        (fun (where,what) -> 
          IDA.msg "%s\n" ("Storing to "^Int64.to_string where^": "^string_of_abstract_bitvector what))
        store_pairs;*)
      
      (* Update the memory accordingly *)
      let mem = List.fold_left (fun f (addr,value) -> abstract_store value addr f) am store_pairs in

      (* Return the memory, and the transformed store expression (don't touch 
         the address component). *)
      (AbsMem(mem),Store(tm,a,et,s))

    | Load(_,_,_)    -> 
      let se = (IRUtil.bits s) lsr 3 in
      if se = 0 then failwith "1-bit load";
      let outval = Array.make (IRUtil.bits s) (AbsZero) in
      (* Load each byte out of memory and OR them together. *)
      let rec aux j =
        if j < se
        then 
          let loaded_value = abstract_load (Int64.add ca (Int64.of_int j)) am in
          for i = (j*8) to (((j+1)*8) - 1) do outval.(i) <- loaded_value.(i land 7) done;
          aux (j+1)
      in 
      (* Return the result and the transformed load expression. *)
      aux 0;
    (*IDA.msg "%s\n" ("Loading from "^Int64.to_string ca^"("^PpIR.ppTypereg s^"): "^string_of_abstract_bitvector outval);*)
      (AbsValue(outval),Load(tm,a,s))
    | _ -> failwith "impossible")
  (* Address wasn't constant; for a load, return top; for a store, return
     the existing memory.  This is not quite sound, but since we only
     track writes that occur in the vicnity of the current stack pointer,
     and we assume that stores to addresses not involving the stack pointer
     do not alias the stack, we can get away with it without sleeping too 
     poorly at night. 
     
     Cases to worry about:
     mov [esp+edi*4], x
     mov [esp+eax], x
     
     We could specifically check for these cases:  if the address expression
     involves esp, but does not evaluate to a constant, then we could return
     top memory.  This is still not sound, however:  consider the ebp register
     aliasing esp.
     *)
  | _ -> (match expr with
    | Load(_,_,_)    -> (AbsValue(make_top s),expr)
    | Store(_,_,_,_) -> (AbsMem(am),expr)
    | _ -> failwith "impossible"))

(* Lookup a variable in the variable context.  If we haven't seen it being 
   assigned yet, we return the default abstract value (top).  If it has been
   assigned already, and it is of variable type, try to replace it with a
   constant. *)
| Var(v) -> 
  let ares = lookup_varctx v in
  let cres = 
    match ares with
    | AbsValue(av) -> 
     (match (make_constant_opt av) with
      | Some(c) -> c
      | None -> expr)
    | _ -> expr
  in
  (ares,cres)

| Let(v,e1,e2) -> 
  (* Save the original value of v. *)
  let orig_v_binding = lookup_varctx v in
  (* Evaluate e1. *)
  let (a1,te1) = bitwise_abstract_interpret e1 in
  (* Update the value of v. *)
  Hashtbl.replace varctx v a1;
  (* Evaluate e2 with the v binding above. *)
  let (a2,te2) = bitwise_abstract_interpret e2 in
  (* Replace the original value of v. *)
  Hashtbl.replace varctx v orig_v_binding;
  (* Return the abstract evaluation and the transformed Let expression. *)
  (a2,Let(v,te1,te2))

(* Perform casting.  Very straightforward. *)
| Cast(k,s,e) -> 
  let src_array,te = bitwise_abstract_interpret e in
  let src_array = unwrap_abstract_value src_array in
  let size_of_dest = IRUtil.bits s in
  let size_of_src  = Array.length src_array in
  let partial_copy init start_in_src copy_len =
    let dest_arr = Array.make size_of_dest init in
    for j = 0 to (copy_len-1) do dest_arr.(j) <- src_array.(start_in_src + j) done;
    dest_arr
  in
  let ares =
    match k with
    (* For unsigned casts, fill the whole array with AbsZero terms, and then
       copy the source values into the lower portion of the destination. *)
    | Unsigned -> partial_copy (AbsZero)                              0 (Array.length src_array)
    (* For signed casts, fill the whole array with the topmost bit of the 
       source, and then copy the lower bits of the source. *)
    | Signed   -> partial_copy src_array.(Array.length src_array - 1) 0 (Array.length src_array)
    (* For low casts, just copy the low values. *)
    | Low      -> partial_copy (AbsZero)                              0 size_of_dest
    (* For high casts, just copy the high values. *)
    | High     -> partial_copy (AbsZero)   (size_of_src - size_of_dest) size_of_dest
  in
  (* Replace with a constant, if possible. *)
  let cres =
    match (make_constant_opt ares) with
    | Some(c) -> c
    | None -> Cast(k,s,te)
  in (AbsValue(ares),cres)

(* Turn a constant directly into an abstract bitvector. *)
| Const(i,s) -> (AbsValue(abstract_bv_of_constant i s),expr)
  
(* Abstract interpret the expressions, and replace them by their transformed
   values.  For all instruction types other than assigns, we throw away the 
   abstract result; for assigns, we update the variable context. *)
let bitwise_abstract_interpret_instr instr =
  match instr with
  | Assign(v,e)  -> let a,expr = bitwise_abstract_interpret e in assign_varctx v a; Assign(v,expr) 
  | Jmp(e)       -> let _,expr = bitwise_abstract_interpret e in Jmp(expr)
  (* Try to turn CJumps into Jmps, if the conditional expression evaluated to
     a constant. *)
  | CJmp(c,t,nt) -> let _,expr = bitwise_abstract_interpret c in 
                   (match expr with
                    | Const(i,TypeReg_1) when i = 1L -> Jmp(t)
                    | Const(i,TypeReg_1) when i = 0L -> Jmp(nt)
                    | Const(_,_) -> failwith "typechecking prevents this jklasjklf"
                    | _ -> CJmp(expr,t,nt))
  | Halt(e)      -> let _,expr = bitwise_abstract_interpret e in Halt(expr)
  | Assert(e)    -> let _,expr = bitwise_abstract_interpret e in Assert(expr)
  | Label(i)     -> instr
  | Comment(s)   -> instr
  | Special(i)   -> failwith ("Cannot abstract interpret special "^PpIR.ppInstr instr)

(* Abstract interpret an entire list of instructions. *)
let bitwise_abstract_interpret_instr_list instrlist =
  List.map 
   (fun i -> 
    (*let abv = unwrap_abstract_value ((Hashtbl.find varctx X86ToIRUtil.vEsp)) in
      let const = make_constant_opt abv in
      IDA.msg "ESP = %s" (string_of_abstract_bitvector abv);
     (match const with
      | Some(Const(i,_)) -> IDA.msg " (%08Lx)\n" i
      | None -> IDA.msg "\n");
      IDA.msg "%s\n" (PpIR.ppInstr i);*)
      bitwise_abstract_interpret_instr i) instrlist 
  
let bitwise_abstract_interpret_ir varlist instrlist =
  Hashtbl.clear varctx;
  List.iter (function | v,Const(i,s) -> Hashtbl.replace varctx v (AbsValue(abstract_bv_of_constant i s)) | _ -> failwith "impossible") varlist;
  let res = bitwise_abstract_interpret_instr_list instrlist in
  Hashtbl.clear varctx;
  res

(* Test the abstract operations on random values n times.  Straightforward. *)
(* As of 5/30/2010 4:47:01 AM, all tests pass for substantial values of n (>100k), 
   although it is revealed that this is a slow process, undoubtedly because of all 
   the array creation and deletion.  If speed turns out to be a critical concern, 
   this whole module is going to need profiling and modification. *)
let test n =
  let ri64 () = Random.int64 Int64.max_int in
  let ri32 () = Random.int64 0x100000000L in
  let ri n    = Random.int n in
  let abv c s = abstract_bv_of_constant c s in
  let abv64 c = abv c TypeReg_64 in
  let abv32 c = abv c TypeReg_32 in
  let test_abstract_binop absbinop concbinop =
    let lhs,rhs = ri64(),ri64() in
    match (make_constant_opt (unwrap_abstract_value (absbinop (AbsValue(abv64 lhs)) (AbsValue(abv64 rhs))))) with
    | Some(Const(c,_)) when c = (concbinop lhs rhs) -> true
    | _ -> false
  in
  let test_abstract_unop absunop concunop =
    let lhs = ri64() in
    match (make_constant_opt (unwrap_abstract_value (absunop (AbsValue(abv64 lhs))))) with
    | Some(Const(c,_)) when c = (concunop lhs) -> true
    | _ -> false
  in
  let test_abstract_shift absshift concshift =
    let lhs,rhs = ri64(),ri 64 in
    match (make_constant_opt (unwrap_abstract_value (absshift (AbsValue(abv64 lhs)) rhs))) with
    | Some(Const(c,_)) when c = (concshift lhs rhs) -> true
    | _ -> false
  in
  let test_abstract_mul absmul concmul =
    let lhs,rhs = ri32(),ri32() in
    match (make_constant_opt (unwrap_abstract_value (absmul (AbsValue(abv32 lhs)) (AbsValue(abv32 rhs))))) with
    | Some(Const(c,_)) when c = (concmul lhs rhs) -> true
    | _ -> false
  in
  for i = 0 to (n-1) do
    if i mod 100 = 0 then print_endline ("Done "^string_of_int i^" tests");
    if not (test_abstract_binop abstract_add  Int64.add                ) then failwith "abstract add failed";
    if not (test_abstract_binop abstract_sub  Int64.sub                ) then failwith "abstract sub failed";
    if not (test_abstract_binop abstract_xor  Int64.logxor             ) then failwith "abstract xor failed";
    if not (test_abstract_binop abstract_and  Int64.logand             ) then failwith "abstract and failed";
    if not (test_abstract_binop abstract_or   Int64.logor              ) then failwith "abstract or failed" ;
    if not (test_abstract_unop  abstract_neg  Int64.neg                ) then failwith "abstract neg failed";
    if not (test_abstract_unop  abstract_not  Int64.lognot             ) then failwith "abstract not failed";
    if not (test_abstract_shift abstract_shl  Int64.shift_left         ) then failwith "abstract shl failed";
    if not (test_abstract_shift abstract_shr  Int64.shift_right_logical) then failwith "abstract shr failed";
    if not (test_abstract_shift abstract_sar  Int64.shift_right        ) then failwith "abstract sar failed";
    if not (test_abstract_mul   abstract_umul Int64.mul                ) then failwith "abstract umul failed";
  done