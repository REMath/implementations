(* Copyright (c) 2013, IMDEA Software Institute.              *)
(* See ../../LICENSE for authorship and licensing information *)


IFDEF INCLUDEOCT THEN
open Printf
open NumAD.DS
open AD.DS
open Logger

let bin_name = ref "output"

module OrdVar = struct
  type t = var
  let compare = Pervasives.compare
end

module VarMap = Map.Make(OrdVar)

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

  (* Change of Dimensions *)
  val add_dims_and_project: oct -> int -> oct
  val add_permute_dims_and_embed: oct -> int -> int array -> oct
  
  (* Pretty-Printers *)
  val foctprinter: (int -> string) -> Format.formatter -> oct -> unit
  val foctdiffprinter: (int -> string) -> Format.formatter -> oct -> oct -> unit

  (* Type Conversion *)
  val num_of_int: int -> num
  val num_of_float: float -> num
  val vnum_of_int: int array -> vnum
  val int_of_num: num -> int option
end

(* help function for trimming a string. *)
let left_pos s len =
  let rec aux i =
    if i >= len then None
    else match s.[i] with
    | ' ' | '\n' | '\t' | '\r' | '{' | '}'-> aux (succ i)
    | _ -> Some i
  in
  aux 0

(* help function for trimming a string. *)
let right_pos s len =
  let rec aux i =
    if i < 0 then None
    else match s.[i] with
    | ' ' | '\n' | '\t' | '\r' | '{' | '}'-> aux (pred i)
    | _ -> Some i
  in
  aux (pred len)
 
(* Trim a string - remove whitespace, '{' and '}' before and after string. *)
let trim s =
  let len = String.length s in
  match left_pos s len, right_pos s len with
  | Some i, Some j -> String.sub s i (j - i + 1)
  | None, None -> ""
  | _ -> assert false


(* Writes a string to a file. *)
let write_file (filename: string) (s: string) : unit = try
  let chan = open_out filename in
  output_string chan s;
  close_out chan
  with Sys_error _ as e ->
      Format.printf "Cannot open file \"%s\": %s\n" filename (Printexc.to_string e)


module type OCTAGON_TEST_DOMAIN = sig
  include AgeAD.S

  val print_to_LattE: t -> string -> unit 
  val set_bin_name: string -> unit
end

module SimpleOctAD (Oct: OCT): OCTAGON_TEST_DOMAIN  = struct
  (* oct = The Octagon; map = Mapping from variables to their position in the octagon *)
  type t = {oct : Oct.oct; map : int VarMap.t; max : int; v2s : var -> string;
    pfn: var -> int}
  
  let count_cstates _ = 
    let minus_one = Big_int.big_int_of_int (-1) in
    (minus_one, minus_one)
    
  let delete_var env var = failwith "SimpleOctAD: delete_var not implemented"
  
  (* Returns a string stating whether a variable v is new or known. *)
  let print_known (octAD: t) (v: var) : string = 
    if (VarMap.mem v octAD.map) then "known" else "new"

  (* Assigns a variable v the value c. *)
  let set_var (octAD: t) (v: var) (c: int) : t = 
    if get_log_level SimpleOctLL = Debug then printf "Setting %s variable %Lx to %d.\n" (print_known octAD v) v c;
    let c = if (c > octAD.max) then octAD.max else c in
    let new_octAD = if not (VarMap.mem v octAD.map) then
      (* Add 1 dimension and add v to the map *)
      {octAD with oct = Oct.add_dims_and_project octAD.oct 1; map = VarMap.add v (Oct.dim octAD.oct) octAD.map}
    else 
       octAD in
    let pos : int = VarMap.find v new_octAD.map in
    let int_array : int array = Array.make (Oct.dim new_octAD.oct + 1) 0 in
    Array.set int_array (pos+1) c;
    let vnum_array : Oct.vnum = Oct.vnum_of_int int_array in 
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
    if get_log_level SimpleOctLL = Debug then printf "Shifting the common variable %Lx from position %d to %d.\n" v1 pos1 pos2;
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
     VarMap.iter (fun v pos -> if get_log_level SimpleOctLL = Debug then printf "Adding missing variable %Lx to %d.\n" v (!new_octAD.max + 1) ;
                               new_octAD := set_var !new_octAD v (!new_octAD.max) 
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
  let init max_val pfn v2s = 
    let _ = Oct.init() in 
    {oct = Oct.universe 0; map = VarMap.empty; max = max_val; v2s = v2s; pfn=pfn}

  (* Sets the upper bound of v to max. *)
  let cap_var (octAD: t) (pos: int) : t = 
    let constr : Oct.constr array = [|Oct.PX (pos,Oct.num_of_int(octAD.max))|] in
    let vopc : Oct.oct = Oct.add_bin_constraints (Oct.universe (Oct.dim octAD.oct)) constr in
    {octAD with oct = Oct.inter octAD.oct vopc}

  (* Increases the variable v by 1. *)
  let inc_var (octAD: t) (v: var) : t = 
    if (VarMap.mem v octAD.map) then
      let pos : int = VarMap.find v octAD.map in
      let int_array : int array = Array.make (Oct.dim octAD.oct + 1) 0 in
      Array.set int_array pos 1;
      Array.set int_array (Oct.dim octAD.oct) 1;
      let vnum_array : Oct.vnum = Oct.vnum_of_int int_array in
      let octAD = {octAD with oct = Oct.assign_var octAD.oct pos vnum_array} in
      cap_var octAD pos
    else
      failwith "Variable to increase has not been initialized using reset_var."

  
  (* Returns Nb octagon or Bot if the octagon is empty.  *)
  let oct_bot (octAD: t) : t add_bottom = 
    if Oct.is_empty octAD.oct then Bot else Nb octAD

  (* Returns the octagons resulting from a comparison of v1 and v2 using the operators < and >. *)
  let comp (octAD: t)  (v1: var) (v2: var) : t add_bottom * t add_bottom = 
    let pos1 : int = VarMap.find v1 octAD.map in
    let pos2 : int = VarMap.find v2 octAD.map in
    let constr_lt : Oct.constr array = [|Oct.PXMY(pos1, pos2, Oct.num_of_int(-1))|] in (* v1 <  v2 =   v1 -v2 <=   -1 *)
    let constr_gt : Oct.constr array = [|Oct.PXMY(pos2, pos1, Oct.num_of_int(-1))|] in (* v1 >  v2 =   v2 -v1 <=   -1 *)
    let oct_lt = Oct.add_bin_constraints octAD.oct constr_lt in
    let oct_gt = Oct.add_bin_constraints octAD.oct constr_gt in
    oct_bot {octAD with oct =  oct_lt}, oct_bot {octAD with oct = oct_gt} 

  let comp_with_val octAD v c = failwith "comp_with_val (needed for FIFO) not yet implemented in octagons" (*TODO*)

  let exact_val octAD v c = failwith "exact_val (needed for PLRU) not yet implemented in octagons" (*TODO*)

  let permute octAD f v = failwith "permute (needed for PLRU) not yet implemented in octagons" (*TODO*)

  (* Computes the union of two octagons. *)
  let join (octAD1: t) (octAD2: t) : t = 
    let (fixed_octAD1, fixed_octAD2) = merge_domains octAD1 octAD2 in
    {fixed_octAD1 with oct = Oct.union fixed_octAD1.oct fixed_octAD2.oct}

  (* Tests whether an octagon is included in a second octagon. *)
  let subseteq (octAD1: t) (octAD2: t) : bool = 
    let (fixed_octAD1, fixed_octAD2) = merge_domains octAD1 octAD2 in
    Oct.is_included_in fixed_octAD1.oct fixed_octAD2.oct

  (* Prints the difference between two octagons. *)
  let print_delta (octAD1: t) (f: Format.formatter) (octAD2: t) : unit =
    match get_log_level SimpleOctLL with
        | Quiet -> ()
        | _ -> let (fixed_octAD1, fixed_octAD2) = merge_domains octAD1 octAD2 in
               Oct.foctdiffprinter (fun i -> fixed_octAD1.v2s (var_at i fixed_octAD1.map)) f fixed_octAD1.oct fixed_octAD2.oct
  
  (* Test whether a is a variable in env *)
  exception NotImplemented
  let is_var env a = raise NotImplemented
  
  (* TODO which widening option? *)
  let widen (octAD1: t) (octAD2: t) : t = 
    let (fixed_octAD1, fixed_octAD2) = merge_domains octAD1 octAD2 in
      {fixed_octAD1 with oct = Oct.widening fixed_octAD1.oct fixed_octAD2.oct Oct.WidenFast}

  (* Functions for LattE *)
  (***********************)

  type term  = Sum of int*int  | Dif of int*int | Single of int

  (* Parses a string s and returns the term it represents. *)
  let get_term (s: string) : term = 
    let split = Str.split (Str.regexp "+") s in
    if (List.length split = 2) then  (* Case: x + y *)
      match split with 
         v1::v2::tl -> Sum (int_of_string v1,int_of_string v2)
       | _ -> failwith "get_term: unexpected case"
    else 
      let split = Str.split (Str.regexp "-") s in
      if (List.length split = 2) then  (* Case: x - y *)
        match split with 
          v1::v2::tl -> Dif (int_of_string v1,int_of_string v2)
        | _ -> failwith "get_term: unexpected case"
      else  (* Case: x *)
        match split with 
          v::tl -> Single (int_of_string v)
        | _ -> failwith "get_term: unexpected case"


  (* Given a constraint, it returns an Array representing it as one line in the LattE input format. *)
  let constr_array (constr: Oct.constr) (n: int) : int array = try
    let myArray = Array.make (n+1) 0 in 
    let set_const c = match Oct.int_of_num c with 
       None -> () 
     | Some i -> Array.set myArray 0 i in
    (match constr with  
       Oct.PX (x,c)  -> set_const c; Array.set myArray (x+1) (-1)    (*   x  <= c *)
     | Oct.MX (x,c)  -> set_const c; Array.set myArray (x+1)   1     (*  -x  <= c *)
     | Oct.PXPY (x,y,c) -> set_const c; Array.set myArray (x+1) (-1); Array.set myArray (y+1) (-1) (*  x+y <= c *)
     | Oct.PXMY (x,y,c) -> set_const c; Array.set myArray (x+1) (-1); Array.set myArray (y+1)   1  (*  x-y <= c *)
     | Oct.MXPY (x,y,c) -> set_const c; Array.set myArray (x+1)   1 ; Array.set myArray (y+1) (-1) (* -x+y <= c *)
     | Oct.MXMY (x,y,c) -> set_const c; Array.set myArray (x+1)   1 ; Array.set myArray (y+1)   1  (* -x-y <= c *)
    );myArray
    with Invalid_argument a -> failwith "constr_arrays"

  (* Saves the constraints in the Latte-format to a file. *)
  let save_constraints (filename: string) (constraints:int array list)  (size: int) : unit = 
    (* Returns a string representing the contents of an int array*)
    let string_of_array a = 
      let b = Buffer.create (2 * size) in 
      Array.iter (fun i -> Buffer.add_string b (string_of_int i); Buffer.add_string b " ") a;
      Buffer.add_string b "\n";
      Buffer.contents b in
    let buffer = Buffer.create (2 * size * List.length constraints) in
    Buffer.add_string buffer (string_of_int (List.length constraints) ^ " " ^ (string_of_int (size + 1)) ^ "\n");
    List.iter (fun a -> Buffer.add_string buffer (string_of_array a)) constraints;
    write_file filename (Buffer.contents buffer) 
  
  exception InvalidExpression
  (* evaluate an expression given in a string, of one of the following types:
     "5", "-5", "5+6", "-5/3" *)
  let eval_expr expr = 
    try
      let num = "[0-9]+" in
      let ops = "[-+*/]" in
      if not (Str.string_match (Str.regexp ("-?"^num^"\\|"^num^ops^num)) expr 0) then
        raise InvalidExpression;
      let get_val x = match x with 
      | Str.Text a -> float_of_string (String.trim a) 
      | _ -> assert false in
      let get_op op = match op with Str.Delim s -> s | _ -> assert false in
      let eval x1 x2 op =
        match op with
        | "+" -> x1 +. x2
        | "-" -> x1 -. x2
        | "*" -> x1 *. x2
        | "/" -> x1 /. x2
        | _ -> raise InvalidExpression in
      let eval_negate op x =
        if op = "-" then -. x
        else raise InvalidExpression in
      match Str.full_split (Str.regexp ops) expr with
      | [x] -> get_val x
      | [op;x] -> 
        eval_negate (get_op op) (get_val x)
      | [x1;op;x2] ->  
        let x1,x2 = (get_val x1), (get_val x2) in
        let op = get_op op in
        eval x1 x2 op
      | [op1;x1;op2;x2] ->
        let x = eval (get_val x1) (get_val x2) (get_op op2) in
        eval_negate (get_op op1) x
      | _ -> raise InvalidExpression
    with InvalidExpression ->
      failwith ("SimpleOctAD: cannot evaluate expression "^expr)

  (* Saves an octagoNumAD in a format that is compatible with LattE integrale. *)
  let print_to_LattE (octAD: t) (filename: string) : unit = 
    (* print a string representation of the octagon to a temporary file. *)
    let tfname, cout = Filename.open_temp_file filename ".tmp" in
    let co = Format.formatter_of_out_channel cout in
    Oct.foctprinter string_of_int co octAD.oct;
    close_out cout;
    (* read the temporary filename into a buffer *)
    let buffer = Buffer.create 1024 in
    let chan = open_in tfname in
    let file_content =
      try
        while true; do
          Buffer.add_string buffer (input_line chan) 
        done; ""
      with End_of_file -> close_in chan; Buffer.contents buffer in
    (* remove the temporary file *)
    Sys.remove tfname;
    
    let parts = Str.split (Str.regexp ",") file_content in
    let trimmed = List.map (fun s -> trim s) parts in  
    let size = Oct.dim octAD.oct in
    let all_constraints = ref [] in
    let non_rel_constraints = ref [] in
    List.iter (fun s -> 
      let split = Str.split (Str.regexp " ") s in 
      assert (List.length split = 3 || List.length split = 5); 
      let constr1,constr2 = match split with 
        lb::_::varpart::_::ub::_ -> (*Case: ineq*)
          let lb = Oct.num_of_float (-.eval_expr lb) in
          let ub = Oct.num_of_float (eval_expr ub) in
          ( match get_term varpart with 
              Single x -> Oct.MX (x,lb), Oct.PX (x,ub)
            | Sum (x,y) -> Oct.MXMY (x,y,lb), Oct.PXPY (x,y,ub)
            | Dif (x,y) -> Oct.MXPY (x,y,lb), Oct.PXMY (x,y,ub)
          )
       |varpart::_::c::_ -> (*Case: eq --> lower bound = upper bound*)
          let lb = Oct.num_of_int (-int_of_string c) in
          let ub = Oct.num_of_int (int_of_string c) in
          ( match get_term varpart with 
              Single x -> Oct.MX (x,lb), Oct.PX (x,ub)
            | Sum (x,y) -> Oct.MXMY (x,y,lb), Oct.PXPY (x,y,ub)
            | Dif (x,y) -> Oct.MXPY (x,y,lb), Oct.PXMY (x,y,ub)
          )
       | _ -> failwith "unexpected Case in octagoNumAD.toLatte"
      in
      let a1 = constr_array constr1 size in
      let a2 = constr_array constr2 size in
      all_constraints := a1 :: a2 :: !all_constraints;
      non_rel_constraints := match constr1 with 
            Oct.MX _ -> a1 :: a2 :: !non_rel_constraints 
          | _ -> !non_rel_constraints 
    ) trimmed;
    save_constraints (filename ^ "_rel.latte") !all_constraints size;
    save_constraints (filename ^ "_non_rel.latte") !non_rel_constraints size 

  let set_bin_name name = 
    bin_name := name


  (* Prints a string representation of the octagon. *)
  let print (f: Format.formatter) (octAD: t) : unit = 
    (*TODO Call print_to_LattE from somewhere else, use bin_name as filename *)
    print_to_LattE octAD !bin_name; 
    Oct.foctprinter (fun i -> octAD.v2s (var_at i octAD.map)) f octAD.oct

  let get_values env v = [] (*failwith "simpleOctAD.get_values not implemented yet"*)
end

module OctAD = SimpleOctAD(Oct)

END
