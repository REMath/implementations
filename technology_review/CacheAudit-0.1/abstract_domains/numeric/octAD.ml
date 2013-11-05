(* Copyright (c) 2013, IMDEA Software Institute.              *)
(* See ../../LICENSE for authorship and licensing information *)


IFDEF INCLUDEOCT THEN
open Printf
open NumAD.DS
open AD.DS
open Logger

let bin_name = ref "output"
let infinity = 0x100000000L
let max_get_var_size = ref 256

module type OCT =
sig
  type oct
  type num
  type vnum
  type wident = WidenFast | WidenZero | WidenUnit | WidenSteps of vnum | PreWiden
  type constr = 
    PX of int*num         (*   x  <= c *)
  | MX of int*num         (*  -x  <= c *)
  | PXPY of int*int*num   (*  x+y <= c *)
  | PXMY of int*int*num   (*  x-y <= c *)
  | MXPY of int*int*num   (* -x+y <= c *)
  | MXMY of int*int*num   (* -x-y <= c *)
  
  (* Octagon creation *)
  val init: unit -> bool
  val universe: int -> oct

  (* Queries *)
  val dim: oct -> int

  (* Tests *)
  val is_empty: oct -> bool
  val is_included_in: oct -> oct -> bool

  (* Operators *)
  val inter: oct -> oct -> oct
  val union: oct -> oct -> oct
  val widening: oct -> oct -> wident -> oct

  (* Transfer Functions *)
  val add_bin_constraints: oct -> constr array -> oct
  val assign_var: oct -> int -> vnum -> oct
  val interv_assign_var: oct -> int -> vnum -> oct

  (* Change of Dimensions *)
  val add_dims_and_project: oct -> int -> oct
  val add_dims_and_embed: oct -> int -> oct
  val add_permute_dims_and_embed: oct -> int -> int array -> oct
  val permute_del_dims: oct -> int -> int array -> oct

  (* Interval functions *)
  val get_bounds: oct -> int -> num*num

  (* Pretty-Printers *)
  val foctprinter: (int -> string) -> Format.formatter -> oct -> unit
  val foctdiffprinter: (int -> string) -> Format.formatter -> oct -> oct -> unit

  (* Type Conversion *)
  val num_of_int: int -> num
  val vnum_of_int: int array -> vnum
  val vnum_of_int_opt: int option array -> vnum
  val int_of_num: num -> int option
  val num_infty: unit -> num
end

module type OCT64 =
sig
  type oct
  type num
  type vnum
  type wident = WidenFast | WidenZero | WidenUnit | WidenSteps of vnum | PreWiden
  type constr = 
    PX of int64*num         (*   x  <= c *)
  | MX of int64*num         (*  -x  <= c *)
  | PXPY of int64*int64*num   (*  x+y <= c *)
  | PXMY of int64*int64*num   (*  x-y <= c *)
  | MXPY of int64*int64*num   (* -x+y <= c *)
  | MXMY of int64*int64*num   (* -x-y <= c *)
  
  (* Octagon creation *)
  val init: unit -> bool
  val universe: int -> oct

  (* Queries *)
  val dim: oct -> int

  (* Tests *)
  val is_empty: oct -> bool
  val is_included_in: oct -> oct -> bool

  (* Operators *)
  val inter: oct -> oct -> oct
  val union: oct -> oct -> oct
  val widening: oct -> oct -> wident -> oct

  (* Transfer Functions *)
  (*val add_bin_constraints: oct -> constr array -> oct*)
  val assign_var: oct -> int -> vnum -> oct
  val interv_assign_var: oct -> int -> vnum -> oct

  (* Change of Dimensions *)
  val add_dims_and_project: oct -> int -> oct
  val add_dims_and_embed: oct -> int -> oct
  val add_permute_dims_and_embed: oct -> int -> int array -> oct
  val permute_del_dims: oct -> int -> int array -> oct

  (* Interval functions *)
  val get_bounds: oct -> int -> num*num

  (* Pretty-Printers *)
  val foctprinter: (int -> string) -> Format.formatter -> oct -> unit
  val foctdiffprinter: (int -> string) -> Format.formatter -> oct -> oct -> unit

  (* Type Conversion *)
  val vnum_of_int64: int64 array -> vnum
  val int64_of_num: num -> int64
end

module Oct64 (Oct:OCT) : OCT64 = struct
  type oct = Oct.oct
  type num = Oct.num
  type vnum = Oct.vnum
  type wident = Oct.wident = WidenFast | WidenZero | WidenUnit | WidenSteps of vnum | PreWiden
  type constr = 
    PX of int64*num         (*   x  <= c *)
  | MX of int64*num         (*  -x  <= c *)
  | PXPY of int64*int64*num   (*  x+y <= c *)
  | PXMY of int64*int64*num   (*  x-y <= c *)
  | MXPY of int64*int64*num   (* -x+y <= c *)
  | MXMY of int64*int64*num   (* -x-y <= c *)

  (* Octagon creation *)
  let init x = Oct.init x

  let universe x = Oct.universe x

  (* Queries *)
  let dim (oct: oct) : int = Oct.dim oct

  (* Tests *)
  let is_empty o = Oct.is_empty o
  let is_included_in o1 o2 = Oct.is_included_in o1 o2

  (* Operators *)
  let inter o1 o2 = Oct.inter o1 o2

  let union o1 o2 = Oct.union o1 o2

  let widening o1 o2 w = Oct.widening o1 o2 w

  (* Transfer Functions *)
  (*val add_bin_constraints: oct -> constr array -> oct*)
  let assign_var (o: oct) (i :int) (vn: vnum) : oct = Oct.assign_var o i vn

  let interv_assign_var (o: oct) (i :int) (vn: vnum) : oct = Oct.interv_assign_var o i vn

  (* Change of Dimensions *)
  let add_dims_and_project (oct: oct) (i: int) : oct = 
    Oct.add_dims_and_project oct i 

  let add_dims_and_embed o i = Oct.add_dims_and_embed o i 

  let add_permute_dims_and_embed (o: oct) (i: int) (a: int array) : oct = 
    Oct.add_permute_dims_and_embed o i a

  let permute_del_dims o i a = Oct.permute_del_dims o i a

  (* Interval functions *)
  let get_bounds o p : num*num = Oct.get_bounds o p

  (* Pretty-Printers *)
  let foctprinter v2s f o = 
    Oct.foctprinter v2s f o

  let foctdiffprinter v2s f o1 o2 = 
    Oct.foctdiffprinter v2s f o1 o2 

  (* Type Conversion *)
  let vnum_of_int64 (a: int64 array) = 
    let a_opt = Array.map 
      (fun i -> if (Int64.compare i (Int64.of_int max_int) = 1) then 
         None 
       else 
         Some (Int64.to_int i)
      ) a in 
    Oct.vnum_of_int_opt a_opt

  let int64_of_num (n: num) : int64 = 
    match Oct.int_of_num n with 
        None   -> infinity 
      | Some x -> Int64.of_int (- x)
end

module OctagoNumAD (Oct: OCT64): NumAD.S = struct
  (* oct = The Octagon; map = Mapping from variables to their position in the octagon *)
  type t = {oct : Oct.oct; map : int VarMap.t; max : int64; v2s : var -> string}

  let var_names _ = failwith "OctNumAD: var_names not implemented"
  
  (* Returns a string stating whether a variable v is new or known. *)
  let print_known (octAD: t) (v: var) : string = 
    if (VarMap.mem v octAD.map) then "known" else "new"

  (* Assigns a variable v the interval [l, h]. *)
  let set_var (octAD: t) (v: var) (l: int64) (h: int64): t = 
    if get_log_level OctLL = Debug then printf "Setting %s variable %Lx to [%Lx, %Lx].\n" (print_known octAD v) v l h;
    let l = if (Int64.compare l octAD.max = 1) then octAD.max else l in
    let h = if (Int64.compare h octAD.max = 1) then octAD.max else h in
    let new_octAD = if not (VarMap.mem v octAD.map) then
      (* Add 1 dimension and add v to the map *)
      {octAD with oct = Oct.add_dims_and_project octAD.oct 1; map = VarMap.add v (Oct.dim octAD.oct) octAD.map}
    else 
       octAD in
    let pos : int = VarMap.find v new_octAD.map in
    let dim = Oct.dim new_octAD.oct in
    let int_array : int64 array = Array.make (2 * dim + 2) (Int64.of_int 0) in
    Array.set int_array (2*dim+1) (Int64.neg l);
    Array.set int_array (2*dim) h;
    let vnum_array : Oct.vnum = Oct.vnum_of_int64 int_array in 
    {new_octAD with oct = Oct.assign_var new_octAD.oct pos vnum_array}

  (* Returns the variable that corresponds to position pos. *)
  (* TODO : maintain the inverse of map *)
  let var_at (pos: int) (map: int VarMap.t) : var = 
    let tmp_map = VarMap.filter (fun v_0 pos_0 -> pos_0 = pos) map in 
      if (not (VarMap.is_empty tmp_map)) then 
        let (v,_) = VarMap.choose tmp_map in 
        v
      else 
        failwith "No variable with that position"

  let non_ex_var (fn: string) (v: var) = 
    failwith (Printf.sprintf "octagoNumAD.%s: non-existent variable %Lx.\n" fn v)

  (* Switch the positions of two variables in a octagoNumAD. *)
  let switch_positions  (octAD: t) (v1: var) (v2: var) : t = 
    let pos1 = try VarMap.find v1 octAD.map with Not_found -> non_ex_var "switch_positions" v1 in
    let pos2 = try VarMap.find v2 octAD.map  with Not_found -> non_ex_var "switch_positions" v2 in
    if get_log_level OctLL = Debug then printf "Shifting the common variable %Lx from position %d to %d.\n" v1 pos1 pos2;
    (* Switch positions in Octagon *)
    let perm = Array.init (VarMap.cardinal octAD.map) (fun i -> i) in
    let switch a i j = let tmp = Array.get a i in Array.set a i (Array.get a j);Array.set a j tmp in
    switch perm pos1 pos2;
    let new_oct = Oct.add_permute_dims_and_embed octAD.oct 0 perm in
    (* Switch positions in VarMap *)
    let new_map = VarMap.add v1 pos2 (VarMap.add v2 pos1 octAD.map) in
    {octAD with oct = new_oct; map = new_map}
    
   (* Shift common variables with octAD2 to the left of octAD1. *)
   let rec common_vars_to_the_left (octAD1: t) (octAD2: t) : t  = 
     let common_vars = VarMap.filter (fun v pos ->  VarMap.mem v octAD2.map) octAD1.map in 
     let missing_in_octAD2 = VarMap.filter (fun v pos -> not (VarMap.mem v octAD2.map)) octAD1.map in 
     if (VarMap.is_empty common_vars || VarMap.is_empty missing_in_octAD2) then 
       octAD1 
     else
       let (max_common_v,max_common_pos) = VarMap.max_binding common_vars in
       let (min_missing_v,min_missing_pos) = VarMap.min_binding missing_in_octAD2 in
       if (max_common_pos > min_missing_pos) then
         common_vars_to_the_left (switch_positions octAD1 max_common_v min_missing_v) octAD2
       else
         octAD1 
   
   (* Reorder common variables according to modelOctAD. 
      Common variables are being assumed to be shifted to the left.
   *)
   let reorder_common_variables (octAD: t) (modelOctAD: t) : t = 
     let new_octAD = ref octAD in 
     VarMap.iter (fun v pos -> 
       if (VarMap.mem v modelOctAD.map) then 
         let correct_pos = VarMap.find v modelOctAD.map in
         if (pos != correct_pos) then 
            new_octAD := switch_positions !new_octAD v (var_at correct_pos !new_octAD.map)
     ) octAD.map;
     !new_octAD

   (* Add variables in octAD2 but not in octAD1 to the end of octAD1. *)
   let add_missing_variables (octAD1: t) (octAD2: t) : t = 
     let missing_in_octAD1 = VarMap.filter (fun v pos -> not (VarMap.mem v octAD1.map)) octAD2.map in 
     let new_octAD = ref octAD1 in 
     VarMap.iter (fun v pos -> if get_log_level OctLL = Debug then printf "Adding missing variable %Lx to %Lx.\n" v (Int64.add !new_octAD.max (Int64.of_int 1)) ;
                               new_octAD := set_var !new_octAD v (!new_octAD.max) (!new_octAD.max) 
                 ) missing_in_octAD1;
     !new_octAD
 
   (* Expands and reorders both domains such that both contain the same variables and their positions match. *)
   let merge_domains (octAD1: t) (octAD2: t) : t * t = 
     (* Shift common variables to the left*)
     let octAD1_a = common_vars_to_the_left octAD1 octAD2 in
     (* Reorder common variables according to oct1 *)
     let octAD2_a = reorder_common_variables octAD2 octAD1_a in
     (* Add missing variables at the end of octAD1 *)
     let octAD1_b = add_missing_variables octAD1_a octAD2_a in
     (* Add missing variables at the end of octAD2 *)
     let octAD2_b = add_missing_variables octAD2_a octAD1_a in
     (* Reorder common variables according to oct1 *)
     (octAD1_b , reorder_common_variables octAD2_b octAD1_b)

  (* Returns an empty octagon respecting a given maximum value. *)
  let init (v2s: var -> string) : t = 
    let _ = Oct.init() in 
    {oct = Oct.universe 0; map = VarMap.empty; max = Int64.of_int max_int; v2s = v2s}

  (* Computes the union of two octagons. *)
  let join (octAD1: t) (octAD2: t) : t = 
    let (fixed_octAD1, fixed_octAD2) = merge_domains octAD1 octAD2 in
    {fixed_octAD1 with oct = Oct.union fixed_octAD1.oct fixed_octAD2.oct}

  (* Prints the difference between two octagons. *)
  let print_delta (octAD1: t) (f: Format.formatter) (octAD2: t) : unit = 
    match get_log_level OctLL with
      | Quiet -> ()
      | _ -> let (fixed_octAD1, fixed_octAD2) = merge_domains octAD1 octAD2 in
             Oct.foctdiffprinter (fun i -> fixed_octAD1.v2s (var_at i fixed_octAD1.map)) f fixed_octAD1.oct fixed_octAD2.oct

  (* Prints a string representation of the octagon. *)
  let print (f: Format.formatter) (octAD: t) : unit = 
    Oct.foctprinter (fun i -> octAD.v2s (var_at i octAD.map)) f octAD.oct

  (* Tests whether an octagon is included in a second octagon. *)
  let subseteq (octAD1: t) (octAD2: t) : bool = 
    let (fixed_octAD1, fixed_octAD2) = merge_domains octAD1 octAD2 in
    Oct.is_included_in fixed_octAD1.oct fixed_octAD2.oct

  (* TODO which widening option? *)
  let widen (octAD1: t) (octAD2: t) : t = 
    let (fixed_octAD1, fixed_octAD2) = merge_domains octAD1 octAD2 in
      {fixed_octAD1 with oct = Oct.widening fixed_octAD1.oct fixed_octAD2.oct Oct.WidenFast}

  let delete_var (octAD: t) (v: var) : t = 
    if (VarMap.mem v octAD.map) then
      let pos1 = VarMap.find v octAD.map in
      let pos2 = Oct.dim octAD.oct in 
      let perm = Array.init (VarMap.cardinal octAD.map) (fun i -> i) in
      let switch a i j = let tmp = Array.get a i in Array.set a i (Array.get a j);Array.set a j tmp in
      switch perm pos1 pos2;
      let new_oct = Oct.permute_del_dims octAD.oct 0 perm in
      {octAD with oct = new_oct; map = VarMap.remove v octAD.map}
    else
      failwith "Variable to increase has not been initialized using set_var."

  let new_var (octAD: t) (v: var) : t = 
    {octAD with oct = Oct.add_dims_and_embed octAD.oct 1}

  (* Returns Nb octagon or Bot if the octagon is empty.  *)
  let oct_bot (octAD: t) : t add_bottom = 
    if Oct.is_empty octAD.oct then Bot else Nb octAD

  let meet (octAD1: t) (octAD2: t) : t add_bottom = 
    let (fixed_octAD1, fixed_octAD2) = merge_domains octAD1 octAD2 in
    oct_bot {fixed_octAD1 with oct = Oct.inter fixed_octAD1.oct fixed_octAD2.oct}

  let is_var (octAD: t) (v: var) : bool = 
    VarMap.mem v octAD.map

  let log_var = failwith "logging not implemented yet"

  let shift = failwith "shift not supported yet"

  let flagop = failwith "flagop not supported yet"

  let update_var = failwith "update_var not supported yet"

  let get_var (octAD: t) (v: var) : (t NumMap.t) add_top = 
    if (VarMap.mem v octAD.map) then
      let pos : int = VarMap.find v octAD.map in
      let num1,num2 = Oct.get_bounds octAD.oct pos in  
      let l = Oct.int64_of_num num1 in
      let h = Oct.int64_of_num num2 in
      if (Int64.compare (Int64.sub h l) (Int64.of_int !max_get_var_size) = -1) then
        let dim = Oct.dim octAD.oct in
        let myMap = ref NumMap.empty in
        let i = ref l in
        while (Int64.compare h !i = 1) do
          let int64_array : int64 array = Array.make (dim + 1) Int64.zero in
          Array.set int64_array (dim) !i; 
          let vnum_array : Oct.vnum = Oct.vnum_of_int64 int64_array in 
          let tmp_oct = Oct.assign_var (Oct.universe (Oct.dim octAD.oct)) pos vnum_array in
          let meet = Oct.inter octAD.oct tmp_oct in
          myMap := NumMap.add !i {octAD with oct = meet} !myMap;
          i := Int64.add !i Int64.one
        done;
        Nt !myMap
      else Tp
    else
      failwith "Variable in get_var has not been initialized using set_var."
end


END



