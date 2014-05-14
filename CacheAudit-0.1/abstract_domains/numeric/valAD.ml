(* Copyright (c) 2013, IMDEA Software Institute.              *)
(* See ../../LICENSE for authorship and licensing information *)

open X86Types
open AbstractInstr
open AD.DS
open NumAD.DS
open Logger

(* We use a module for the options so that we can have different instances in the same analysis *)
module type VALADOPT = sig
  val max_get_var_size:int
  val max_set_size:int
end

module ValADOptForMemory = struct
  let max_get_var_size = 256
  let max_set_size = 32
end

let logFile = ref None

module Make (O:VALADOPT) = struct
(* A basic variable contains a 32 bits unsigned integer. *)

  (* Type of the abstract elements representing one variable *)
  type var_t = FSet of NumSet.t | Interval of int64*int64

  let min_elt = 0L
  let max_elt = 0xffffffffL
  let two32 = 0x100000000L
  let top = Interval(min_elt, max_elt)
  let is_top l h = l=min_elt && h=max_elt

  let rec interval_to_set l h = if l>h then NumSet.empty
    else NumSet.add l (interval_to_set (Int64.succ l) h)
  let set_to_interval s = Interval(NumSet.min_elt s, NumSet.max_elt s)
  let zero = FSet(NumSet.singleton 0L)
  let range_over (l,h) r =
    let range = Int64.sub h l in
    range > (Int64.of_int max_int) || Int64.to_int range > r 

  type t = var_t VarMap.t

  let var_names env = 
    let keys,_ = List.split (VarMap.bindings env) in 
    List.fold_left (fun set elt -> NumSet.add elt set) NumSet.empty keys

  
(* TODO put this into the type t *)
  let variable_naming = ref(fun x -> "")

  let pp_var_vals fmt = function
  | FSet vals -> Format.fprintf fmt "@[{";
      NumSet.iter (fun v -> Format.fprintf fmt "%Ld @," v) vals;
      Format.fprintf fmt "}@]"
  | Interval(l,h) -> if is_top l h then Format.fprintf fmt "Top"
                     else Format.fprintf fmt "@[[%Ld, %Ld]@]" l h

  let var_vals_equal x1 x2 = match x1,x2 with
  | FSet s1, FSet s2 -> NumSet.equal s1 s2
  | Interval(l1,h1), Interval(l2,h2) -> l1=l2 && h1=h2
  | FSet s1, Interval(l2,h2) | Interval(l2,h2), FSet s1 ->
      NumSet.min_elt s1 = l2 && NumSet.max_elt s1 = h2 && 
      NumSet.equal s1 (interval_to_set l2 h2)

  let print_one_var fmt v vals  = Format.fprintf fmt "@[%s in %a@]@;"
    (!variable_naming v) pp_var_vals vals

  let log_var v env= 
    let file = match !logFile with
      | None -> let f = (open_out "log.txt") in logFile := Some (f); f
      | Some f -> f
    in let log_var_vals = function
      | FSet vals -> Printf.fprintf file "{";
          NumSet.iter (fun v -> Printf.fprintf file "%Ld " v) vals;
          Printf.fprintf file "}"
      | Interval(l,h) -> if is_top l h then Printf.fprintf file "Top"
                         else Printf.fprintf file "[%Ld, %Ld]" l h
    in Printf.fprintf file "%s " (!variable_naming v);
    log_var_vals (VarMap.find v env);
    Printf.fprintf file "\n"

  let print fmt env = Format.fprintf fmt "@[<hov 0>";
    VarMap.iter (print_one_var fmt) env;
    Format.fprintf fmt "@]"

  (* We just print differing and new variables *)
  let print_delta env1 fmt env2 = match get_log_level ValLL with
    | Debug -> Format.fprintf fmt "@[";
           VarMap.iter (fun v vals -> try 
             let old_vals = VarMap.find v env1  in
             if not(var_vals_equal old_vals vals) then  print_one_var fmt v vals
             with Not_found -> print_one_var fmt v vals) env2;
           Format.fprintf fmt "@]"
    | _ -> ()

  (* precision : int64 -> int64, returns the 32 least significant bits of a number *)
  let precision by n = 
    match by with
      | 32 -> Int64.logand n 0xFFFFFFFFL
      | 8 -> Int64.logand n 0xFFL
      | _ -> failwith "precision: wrong argument"

  let set_map f set = NumSet.fold (fun x -> NumSet.add (f x)) set NumSet.empty

(* Mask values and shift them to the right *)
  let apply_mask mask shift x =
    Int64.shift_right (Int64.logand mask x) shift

  let mask_vals msk v = 
   let (cv_mask, cv_shift) = mask_to_intoff msk in
   let am = apply_mask cv_mask cv_shift in
   match v with
   | FSet s -> FSet(set_map am s)
   | Interval(l,h) -> 
      let ml = if h>cv_mask then 0L else am l in
      let mh = if l>cv_mask then 0L (*in that case we have also h>cv_mask *)
        else if h>cv_mask then am cv_mask
        else am h in
      assert(ml<=mh);
      Interval(ml,mh)

  (* Flag setting functions *)
  let flag_carry res =
    let upper_bound = Int64.shift_left Int64.one 32 in
    let lower_bound = 0L in
    res < lower_bound || res >= upper_bound
  let flag_carry_shift sop original result offset =
    let carry = match sop with
      Shl -> Int64.logand result (Int64.shift_left Int64.one 32)
    | Shr | Sar ->
        let mask = Int64.shift_left Int64.one (offset - 1) in
        Int64.logand mask original
    (* TODO: check if this is how the CF flag is set for ROL/ROR *)
    | Ror -> Int64.logand original 1L
    | Rol -> Int64.logand original (Int64.shift_left 1L 31)
    in
    carry <> Int64.zero
  let flag_zero res = ((precision 32 res) = 0L)

  (* set_or_interval given two bounds either returns an interval or a set if its size is less than O.max_set_size *)
  let set_or_interval l h = if range_over (l,h) O.max_set_size then Interval(l,h) else FSet (interval_to_set l h)

  let init v2s = variable_naming:=v2s; VarMap.empty

  let new_var m v = VarMap.add v top m

  let delete_var m v = VarMap.remove v m

  let is_var m vn = VarMap.mem vn m

  let get_var m v = try (match VarMap.find v m with
    | FSet l -> Nt (NumSet.fold (fun vl env -> NumMap.add vl (VarMap.add v (FSet (NumSet.singleton vl)) m) env) l NumMap.empty)
    | Interval(l,h) -> if range_over (l,h) O.max_get_var_size then Tp
        else
          let rec f l h = if l>h then NumMap.empty
            else NumMap.add l (VarMap.add v (FSet (NumSet.singleton l)) m) 
                   (f (Int64.succ l) h) in
          Nt(f l h)
  ) with Not_found -> failwith  (Printf.sprintf "valAD.get_var: non-existent variable %Lx\n" v)

  let set_var m v l h = VarMap.add v (set_or_interval l h) m

  let get_vals c m = match c with
    Cons cs -> FSet (NumSet.singleton (precision 32 cs))
  | VarOp v -> try VarMap.find v m
               with Not_found -> failwith "valAD.get_vals: inexistent variable"

  let same_vars v cv = match cv with VarOp v2 -> v=v2 | Cons _ -> false

  let var_join x y = match x,y with
  | FSet s1, FSet s2 -> let s = NumSet.union s1 s2 in
      if NumSet.cardinal s > O.max_set_size then set_to_interval s else FSet s
  | Interval(l,h), FSet s | FSet s, Interval(l,h) -> 
      Interval(min l (NumSet.min_elt s), max h (NumSet.max_elt s))
  | Interval(l1,h1), Interval(l2,h2) -> Interval(min l1 l2, max h1 h2)

  let join (x:t) (y:t) =
    let f k a b = match a,b with
        | Some c, Some d -> Some(var_join c d)
        (* f should never enter this case *)
        | _, None | None, _ -> failwith "Disjoint variables in valAD.join"
    in
    VarMap.merge f x y
  
  let var_meet x y = match x,y with
  | FSet s1, FSet s2 -> let s = NumSet.inter s1 s2 in
      if NumSet.is_empty s then raise Bottom else FSet s
  | Interval(l,h), FSet s | FSet s, Interval(l,h) -> 
      let rs = NumSet.filter (fun x -> x>=l && x<=h) s in
      if NumSet.is_empty rs then raise Bottom else FSet rs
  | Interval(l1,h1), Interval(l2,h2) ->
      let l = max l1 l2 in
      let h = min h1 h2 in
      if l > h then raise Bottom 
      else if range_over (l,h) O.max_set_size then Interval(l,h)
      else FSet(interval_to_set l h)

  let meet x y =
    let f k a b = match a,b with
        | Some c, Some d -> Some (var_meet c d)
        (* f should never enter this case *)
        | _, None | None, _ -> failwith "Disjoint variables in valAD.meet"
    in
    try Nb (VarMap.merge f x y)
    with Bottom -> Bot

  let var_widen x y = match x, y with
  | FSet s1, FSet s2 -> let s = NumSet.union s1 s2 in
      if NumSet.cardinal s > O.max_set_size then set_to_interval s else FSet s
  | Interval(l,h), FSet s | FSet s, Interval(l,h) ->
      Interval(min l (NumSet.min_elt s), max h (NumSet.max_elt s))
  | Interval(l1,h1), Interval(l2,h2) -> 
     let l = if l2<l1 then min_elt else l1 in
     let h = if h2>h1 then max_elt else h1 in
     Interval(l,h)

  let widen x y =
    (*let pp_one_var v fmt k = print_one_var fmt k v in*)
    let f k a b = match a,b with
        | Some c, Some d -> Some(var_widen c d)
        (* f should never enter this case *)
        | _, None | None, _ -> failwith "Disjoint variables in valAD.widen"
    in
    VarMap.merge f x y

  let var_subseteq x y = match x,y with
 | FSet s1, FSet s2 -> NumSet.subset s1 s2
 | FSet s, Interval(l,h) -> NumSet.min_elt s >= l && NumSet.max_elt s <= h
 | Interval(l,h), FSet s -> 
    let res = ref true in
    let i = ref l in
    while(!res && !i<=h) do res:=NumSet.mem !i s; i:= Int64.succ !i done;
    !res
 | Interval(l1,h1), Interval(l2,h2) -> l1>=l2 && h1<=h2

  exception Not_included
  let subseteq x y =
    let f k a b = match a,b with
      | Some c, Some d -> if var_subseteq c d then None else raise Not_included
       | Some c, _ -> raise Not_included
       | _, Some d -> None
       | _, _ -> None
     in
     try (ignore (VarMap.merge f x y); true)
     with Not_included -> false

  (* Functions used by update_var *)
  let arithop_to_int64op = function
    | Add -> Int64.add
    | Addc -> Int64.add
    | And -> Int64.logand
    | CmpOp -> failwith "CmpOp should be handled by flagop instead of memop"
    | Or -> Int64.logor
    | Sub -> Int64.sub
    | Subb -> Int64.sub
    | Xor -> Int64.logxor
    (* | ADiv -> Int64.div *)
    (* | ARem -> Int64.rem *)

  let add_CF y cf = function
    | Addc | Subb -> Int64.add y cf
    | _ -> y

  let make_set_from_list = List.fold_left (fun s x -> NumSet.add x s) NumSet.empty

  let go_to_interval s = if NumSet.cardinal s > O.max_set_size then set_to_interval s else FSet s

  type position = TT | TF | FT | FF

  (* interval_operation takes an operation and two intervals and returns the resulting
   * interval after applying the operation (which must be monotonic) *)
  let interval_operation oper x y = match x,y with 
    | Interval (dl,dh), Interval (sl,sh) ->
        let bound f = List.fold_left f (oper dl sl) [oper dl sh; oper dh sl; oper dh sh] in
        let lb,ub = bound min, bound max in
        assert(ub >= lb); Interval (lb,ub)
    | _,_ -> raise (Invalid_argument "interval_operation")

  (* Wrapper function for var_meet; we need the intersection without raising Bottom *)
  let var_meet_ab x y = try (Nb (var_meet x y)) with Bottom -> Bot

  (* Applies op to each element of the FSet or the bounds of the Interval *)
  let mapt op = function
    | FSet s -> FSet (set_map op s)
    | Interval(l,h) -> Interval(op l, op h)

  (* Functions for bitwise interval operations 
   * Based on http://www.cs.utah.edu/~regehr/papers/lctes06_2/ *)
  let coef x k =
    let twok = Int64.shift_left 1L k in
    Int64.div x twok

  (* Zeroes the k-th bit of the interval *)
  let killBit interval k =
    let even x = (Int64.rem x 2L = 0L) in
    let twok = Int64.shift_left 1L k in
    match interval with
    | Interval(l,h) -> begin
        let ch = coef h k in
        let cl = coef l k in
        let ub = 
          if even ch then h
          else if l < (Int64.mul ch twok) then Int64.mul ch twok
          else Int64.sub h twok
        in
        let lb =
          if not (even cl) then Int64.sub l twok
          else if h >= Int64.mul twok (Int64.succ cl) then Int64.mul cl twok
          else l
        in
        Interval(lb,ub)
    end
    | _ -> raise (Invalid_argument "killBit")

  let isBitSet x bit = (Int64.logand (Int64.shift_left 1L bit) x) <> Int64.zero

  let get_bounds = function
    | Interval (l,h) -> (l,h)
    | _ -> raise (Invalid_argument "get_bounds")

  (* Function to compute the "contributing" bits of the interval *)
  let loopBound ai bi bound =
    let testbound = bound (get_bounds bi) in
    let newai = ref ai in
    for i = 31 downto 0 do
      if isBitSet testbound i
        then newai := killBit !newai i
    done;
    bound (get_bounds !newai)

  (* Bitwise or for intervals *)
  let interval_or a b =
    match a,b with
    | Interval(al,ah), Interval (bl,bh) ->
        let lma,lmb = loopBound a b fst, loopBound b a fst in
        let hma,hmb = loopBound a b snd, loopBound b a snd in
        let lowerBound = min (Int64.logor al lmb) (Int64.logor bl lma) in
        let upperBound = max (Int64.logor ah hmb) (Int64.logor ah hma) in
        Interval (lowerBound, upperBound)
    | _,_ -> raise (Invalid_argument "interval_or")

  (* Bitwise not for intervals *)
  let interval_not = function
    | Interval(l,h) ->
        let f x = precision 32 (Int64.lognot x) in
        Interval(f h, f l)
    | _ -> raise (Invalid_argument "interval_not")

  (* Bitwise and for intervals defined using or and not *)
  let interval_and a b =
    (* a & b = not (not a | not b) *)
    interval_not (interval_or (interval_not a) (interval_not b))

  (* interval_update takes a flg : position = {TT,...,FF}, an arith_op aop,
   * the Int64 operation oper and two intervals *)
  let interval_update flg aop oper di si = 
    match aop with
      Add | Addc ->
        begin
          (* Interval after operation *)
          let inter = interval_operation oper di si in
          let modulo = fun x -> Int64.sub x two32 in
          (* Intersection of the interval with differentes ranges *)
          let meetZero = var_meet_ab inter (FSet (NumSet.singleton min_elt)) in
          let meetNormal = var_meet_ab inter (Interval (Int64.succ min_elt, max_elt)) in
          let meet2_32 = var_meet_ab inter (FSet (NumSet.singleton two32)) in
          let meetOver = var_meet_ab inter (Interval (Int64.succ two32, Int64.sub (Int64.add two32 two32) 2L)) in
          (match flg,meetZero,meetNormal,meet2_32,meetOver with
          (* Can set CF & ZF only if result is 2^32 *)
          | TT,_,_,Nb z2,_ -> mapt modulo z2
          (* Can set CF & not ZF if ub is > than 2^32 and does not contain zero *)
          | TF,_,Nb n,_,Nb o -> var_join n (mapt modulo o)
          | TF,_,Bot,_,Nb o -> mapt modulo o
          (* Can set ZF only if result only contains zero *)
          | FT,Nb z,_,_,_ -> z
          (* Can set not CF and not ZF if interval is in normal range *)
          | FF,_,Nb n,_,_ -> n
          | _,_,_,_,_ -> raise Bottom)
        end
    | Sub | Subb ->
        begin
          let inter = interval_operation oper di si in
          let modulo = fun x -> Int64.add two32 x in
          (* Intersection of the interval with differentes ranges *)
          let meetZero = var_meet_ab inter (FSet (NumSet.singleton min_elt)) in
          let meetNormal = var_meet_ab inter (Interval (Int64.succ min_elt, max_elt)) in
          let meetUnder = var_meet_ab inter (Interval (Int64.pred min_elt, Int64.sub 1L two32)) in
          (match flg,meetUnder,meetZero,meetNormal with
          (* CF & ZF not possible *)
          | TT,_,_,_ -> raise Bottom
          (* CF not ZF if under *)
          | TF,Nb u,_,_ -> mapt modulo u
          (* not CF & ZF if only zero *)
          | FT,_,Nb z,_ -> z
          (* not CF not ZF if no zero and no under *)
          | FF,_,_,Nb n -> n
          | _,_,_,_ -> raise Bottom)
        end
    (* Bitwise operations can only set the zero flag *)
    | And -> 
        let nint = interval_and di si in
        let meetZero = var_meet_ab nint (FSet (NumSet.singleton min_elt)) in
        let meetNormal = var_meet_ab nint (Interval (Int64.succ min_elt, max_elt)) in
        (match flg,meetZero,meetNormal with
        | FT,Nb z,_ -> z
        | FF,_,Nb n -> n
        | _,_,_ -> raise Bottom) 
    | Or -> 
        let nint = interval_or di si in
        let meetZero = var_meet_ab nint (FSet (NumSet.singleton min_elt)) in
        let meetNormal = var_meet_ab nint (Interval (Int64.succ min_elt, max_elt)) in
        (match flg,meetZero,meetNormal with
        | FT,Nb z,_ -> z
        | FF,_,Nb n -> n
        | _,_,_ -> raise Bottom)
    | Xor ->
        (* a xor b = (a & not b) or (b & not a) *)
        let f a b = interval_and a (interval_not b) in
        let nint = interval_or (f di si) (f si di) in
        let meetZero = var_meet_ab nint (FSet (NumSet.singleton min_elt)) in
        let meetNormal = var_meet_ab nint (Interval (Int64.succ min_elt, max_elt)) in
        (match flg,meetZero,meetNormal with
        | FT,Nb z,_ -> z
        | FF,_,Nb n -> n
        | _,_,_ -> raise Bottom)
    | CmpOp -> failwith "interval_update: CmpOp"

  (** Arguments: environment, destination var., dest. var. mask, source var., src. var. mask *)
  let update_var m dstvar mkvar srcvar mkcvar op = match op with
    | Op Xor when same_vars dstvar srcvar -> (*Then the result is 0 *)
              Bot, Bot, Nb(VarMap.add dstvar zero m), Bot
    | _ ->
    let src_vals = get_vals srcvar m in
    let dst_vals = VarMap.find dstvar m in
    let create_m flg cf test = match mkvar, mkcvar with
      (* 32 bits -> 32 bits : MOV & Arith *)
      NoMask, NoMask ->
        begin
          match op with
            Move -> Nb (VarMap.add dstvar src_vals m)
          | Op o ->
              let oper = arithop_to_int64op o in
              (* Add carry flag value to operation if it's either Addc or Subb *)
              let oper = fun x y -> oper x (add_CF y cf o) in
              begin
                match dst_vals, src_vals with
                | FSet ds, FSet ss ->
                    let doOp x = NumSet.fold 
                    (fun y r -> 
                      let result = oper x y in
                      if test result then NumSet.add (precision 32 (result)) r else r
                    ) ss NumSet.empty
                    in
                    let finalSet = NumSet.fold (fun x s -> NumSet.fold NumSet.add (doOp x) s) ds NumSet.empty in
                    if NumSet.is_empty finalSet 
                       then Bot
                       else Nb (VarMap.add dstvar (go_to_interval finalSet) m)
                (* We convert sets into intervals in order to perform the operations;
                 * interval_update may return either FSet or Interval *)
                | Interval (l,h), FSet s ->
                    (try (
                      let new_dst = interval_update flg o oper (Interval (l,h)) (set_to_interval s) in
                      Nb (VarMap.add dstvar new_dst m)
                    ) with Bottom -> Bot)
                | FSet s, Interval(l,h) ->
                    (try (
                      let new_dst = interval_update flg o oper (set_to_interval s) (Interval (l,h)) in
                      Nb (VarMap.add dstvar new_dst m)
                    ) with Bottom -> Bot)
                | Interval (dl,dh), Interval (sl,sh) ->
                    (try (
                      let new_dst = interval_update flg o oper (Interval (dl,dh)) (Interval (sl,sh)) in
                      Nb (VarMap.add dstvar new_dst m)
                    ) with Bottom -> Bot)
              end
        end
      (* 8 -> 32 : MOVZX *)
    | NoMask, Mask msk ->
        let src_vals = mask_vals msk src_vals in
        Nb (VarMap.add dstvar src_vals m)
      (* 8 -> 8 : only MOVB *)
    | Mask mkv, Mask mkc ->
        begin
          match op with
            Move -> 
              begin
                match dst_vals, src_vals with
                | FSet ds, FSet ss_unmasked ->
                    let (c_mask, c_shift) = mask_to_intoff mkc in
                    (* Nullify everything but the 8 bits corresponding to the mask *)
                    let ss_shifted = set_map (fun x -> Int64.logand x c_mask) ss_unmasked in
                    (* Then shift it to the first 8 bits *)
                    let ss = set_map (fun x -> Int64.shift_right x c_shift) ss_shifted in
                    let (v_mask, v_shift) = mask_to_intoff mkv in
                    (* Align cv values in order to write them into v *)
                    let cvSet = set_map (fun x -> Int64.shift_left x v_shift) ss in
                    (* Nullify the 8 bits corresponding to the mask *)
                    let varSet = set_map (fun x -> Int64.logand (Int64.lognot v_mask) x) ds in
                    (* Create a list of set combining all the posible values with the mask in place *)
                    let doOp x = set_map (fun y -> Int64.logor x y) varSet in
                    let setList = NumSet.fold (fun x r -> doOp x :: r) cvSet [] in
                    (* Unite all the sets *)
                    let finalSet = List.fold_left NumSet.union NumSet.empty setList in
                    Nb (VarMap.add dstvar (go_to_interval finalSet) m)
                | _, _ -> Nb (VarMap.add dstvar top m)
              end
          | Op o -> failwith "ValAD.update_var: operations between 8-bit values not implemented"
        end
    | _, _ -> failwith "ValAD.update_var: operation from 32 bits to 8 bits"
    in
    (* When we are passed the environment we don't know anything about the carry flag,
     * so when we have an Addc or Subb we need to consider two cases: CF set and CF not set *) 
    let noFlag_m = create_m FF 0L (fun _ -> true) in (* flag position doesn't matter *)
    let final_m flg test = 
      match op with
      | Move -> noFlag_m
      | Op Subb | Op Addc -> lift_combine join (create_m flg 1L test) (create_m flg 0L test)
      | _ -> create_m flg 0L test
    in
    (
      final_m TT (fun x -> flag_carry x && flag_zero x),
      final_m TF (fun x -> flag_carry x && not (flag_zero x)),
      final_m FT (fun x -> not (flag_carry x) && flag_zero x),
      final_m FF (fun x -> not (flag_carry x) && not (flag_zero x))
    )

  (* interval_flag_test takes two intervals and a flag combination and returns
   * the corresponding intervals *)
  let interval_flag_test pos op di si =
    match op with
    | Sub ->
        let dl,dh = get_bounds di in
        let sl,sh = get_bounds si in
        (* Intersection between the two intervals *)
        let meetZF = var_meet_ab di si in
        begin
          match pos with
          | TT -> raise Bottom
          | TF -> (* We should have [dl, min(dh,sh-1)] and [max(dl+1,sl), sh] *)
              let ndh = min dh (Int64.pred sh) in
              let nsl = max (Int64.succ dl) sl in
              if ndh < dl || nsl > sh then raise Bottom
              else (set_or_interval dl ndh),(set_or_interval nsl sh)
          | FT -> (* meet <> empty then ZF can be set *)
              begin
                match meetZF with
                | Bot -> raise Bottom
                | Nb z -> z,z
              end
          | FF -> 
              let nsh = min (Int64.pred dh) sh in
              let ndl = max dl (Int64.succ sl) in
              if ndl > dh || nsh < sl then raise Bottom
              else (set_or_interval ndl dh),(set_or_interval sl nsh)
        end
    | _ -> failwith "interval_flag_test: TEST instruction for intervals not implemented yet"

  (* flagop *)
  let flagop m fop dst src =
    let dvals = get_vals dst m in
    let svals = get_vals src m in
    match dvals,svals with
      FSet dvals, FSet svals ->
        let op = arithop_to_int64op fop in
        (* Combines two sets of values and only keeps those combinations that satisfy test;
         * returns the tuples with the values that satisfy test *)
        let setComb d s test =
          let doOp x = NumSet.fold (fun y r -> if test (op y x) then (y,x) :: r else r) d [] in
          List.concat (NumSet.fold (fun x r -> (doOp x) :: r) s [])
        in
        (* Create an environment given a test function *)
        let create_m test =
        (* Do all the possible combinations *)
          let combs = setComb dvals svals test in
          (* If combs is empty, it means that there are no values that satisfy test.
           * Then we return Bottom *)
          if combs = []
            then Bot
            else Nb (
              (* Create the enviroment by adding the values obtained to the VarMap *)
              let ld,ls = List.split combs in
              let new_m = VarMap.add (consvar_to_var dst) (FSet (make_set_from_list ld)) m in
              (match src with
              | VarOp x -> VarMap.add x (FSet (make_set_from_list ls)) new_m
              | Cons _ -> new_m)
            )
        in 
        (
          create_m (fun x -> flag_carry x && flag_zero x),
          create_m (fun x -> flag_carry x && not (flag_zero x)),
          create_m (fun x -> not (flag_carry x) && flag_zero x),
          create_m (fun x -> not (flag_carry x) && not (flag_zero x))
        )
    | Interval(dl,dh), FSet s -> 
        let ift pos = interval_flag_test pos fop dvals (set_to_interval s) in
        let newm pos = VarMap.add (consvar_to_var dst) (fst (ift pos)) m in
        let create_m pos = 
          (match src with
          | VarOp x -> VarMap.add x (snd (ift pos)) (newm pos)
          | Cons _ -> newm pos)
        in
        let finalm pos = try (Nb (create_m pos)) with Bottom -> Bot in
        (finalm TT, finalm TF, finalm FT, finalm FF)
    | FSet s, Interval (sl,sh) -> 
        let ift pos = interval_flag_test pos fop (set_to_interval s) svals in
        let newm pos = VarMap.add (consvar_to_var dst) (fst (ift pos)) m in
        let create_m pos = 
          (match src with
          | VarOp x -> VarMap.add x (snd (ift pos)) (newm pos)
          | Cons _ -> newm pos)
        in
        let finalm pos = try (Nb (create_m pos)) with Bottom -> Bot in
        (finalm TT, finalm TF, finalm FT, finalm FF)
    | Interval(dl,dh), Interval (sl,sh) -> 
        (* interval_flag_test returns the two intervals *)
        let ift pos = interval_flag_test pos fop dvals svals in
        (* Add the interval of dst to the enviroment *)
        let newm pos = VarMap.add (consvar_to_var dst) (fst (ift pos)) m in
        (* If src is a variable, add interval of src to env *)
        let create_m pos = 
          (match src with
          | VarOp x -> VarMap.add x (snd (ift pos)) (newm pos)
          | Cons _ -> newm pos)
        in
        (* If not bottom, we return the enviroment *)
        let finalm pos = try (Nb (create_m pos)) with Bottom -> Bot in
        (finalm TT, finalm TF, finalm FT, finalm FF)

  let rotate_left value offset =
    let bin = Int64.shift_left value offset in
    let bout = Int64.shift_right_logical value (32 - offset) in
    Int64.logor (precision 32 bin) (precision 32 bout)

  let rotate_right value offset =
    let bin = Int64.shift_right_logical value offset in
    let bout = Int64.shift_left value (32 - offset) in
    Int64.logor (precision 32 bin) (precision 32 bout)

  let shift_operator = function
    | Shl -> fun x o -> Int64.shift_left x (Int64.to_int o)
    | Shr -> fun x o -> Int64.shift_right_logical x (Int64.to_int o)
    (* In order to preserve the sign, we need to convert to int32 *)
    | Sar -> fun value off -> Int64.of_int32 (Int32.shift_right (Int64.to_int32 value) (Int64.to_int off))
    | Ror -> fun x o -> rotate_right x (Int64.to_int o)
    | Rol -> fun x o -> rotate_left x (Int64.to_int o)
  
  (* shift *)
  (* Shift the values of the variable dst using the offsets given by soff *)
  let shift m sop dst soff mk = 
    let vals = VarMap.find dst m in
    let off_vals = get_vals soff m in
    let offsets = (match mk with NoMask -> off_vals | Mask msk -> mask_vals msk off_vals) in
    let operator = shift_operator sop in
    let create_m test = 
      match vals, offsets with
      | FSet d, FSet o ->
          let doOp x = NumSet.fold 
          (fun y s -> 
            let result = operator x y in
            if test sop result x (Int64.to_int y)
              then NumSet.add (precision 32 result) s
              else s)
          o NumSet.empty in
          let finalSet = NumSet.fold (fun x s -> NumSet.fold NumSet.add (doOp x) s) d NumSet.empty in
          if NumSet.is_empty finalSet
            then Bot
            else Nb (VarMap.add dst (go_to_interval finalSet) m)
      | Interval(l,h), FSet o -> (* This doesn't work with rotate; return Top if rotate *)
          let bound f b e = NumSet.fold (fun x r -> f (operator b x) r) o e in
          let lb, ub = bound min l max_elt, bound max h min_elt in
          (* TODO : flag test *)
          begin
            match sop with
              Ror | Rol -> Nb (VarMap.add dst top m)
            | _ -> if ub < lb then Bot else Nb (VarMap.add dst (Interval(lb,ub)) m)
          end
      | _, _ -> failwith "ValAD.shift: case not implemented"
    in
    (
      create_m (fun sop rs og os -> flag_carry_shift sop rs og os && flag_zero rs),
      create_m (fun sop rs og os -> flag_carry_shift sop rs og os && not (flag_zero rs)),
      create_m (fun sop rs og os -> not (flag_carry_shift sop rs og os) && flag_zero rs),
      create_m (fun sop rs og os -> not (flag_carry_shift sop rs og os) && not (flag_zero rs))
    )

end

