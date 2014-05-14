(*
 *  This file is part of WhileAnalyser
 *  Copyright (c)2005-2008 INRIA Rennes - Bretagne Atlantique
 *  David Pichardie <first.last@irisa.fr>
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *)

open Syntax

module Make =
struct

  type z' =
    | Z of Num.num
    | Infty_pos
    | Infty_neg

  type interval = z' * z'

  let min = function
    | (a0, b) -> a0
	
  let max = function
    | (a0, a1) -> a1

  let min_z' x y =
    match x with
      | Infty_pos -> y
      | Infty_neg -> Infty_neg
      | Z x -> 
	  (match y with
	     | Infty_pos -> Z x
	     | Infty_neg -> Infty_neg
	     | Z y -> Z (Num.min_num x y))

  let max_z' x y =
    match x with
      | Infty_pos -> Infty_pos
      | Infty_neg -> y
      | Z x -> 
	  (match y with
	     | Infty_pos -> Infty_pos
	     | Infty_neg -> Z x
	     | Z y -> Z (Num.max_num x y))
	    
  let le_test x y =
    match (x,y) with
      | (Infty_neg,_) -> true
      | (Infty_pos,Infty_pos) -> true
      | (Infty_pos,_) -> false
      | (Z x,Infty_neg) -> false
      | (Z x,Infty_pos) -> true
      | (Z x,Z y) -> Num.le_num x y


  module L =
  struct 


    type t = interval option
	

    let string_of_z' = function
      | Infty_pos -> "+oo"
      | Infty_neg -> "-oo"
      | Z n -> Num.string_of_num n

    let to_string = function
      | None -> "bot"
      | Some ((a,b)) -> Printf.sprintf "[%s,%s]" (string_of_z' a) (string_of_z' b)

    let join i1 i2 =
      match (i1, i2) with
	| (Some i1, Some i2) ->
	    Some ((min_z' (min i1) (min i2),max_z' (max i1) (max i2)))
	| (None,i2) -> i2
	| (i1,None) -> i1

    let meet i1 i2 =
      match (i1, i2) with
	| (Some i1, Some i2) ->
	    let max = min_z' (max i1) (max i2)
	    and min = max_z' (min i1) (min i2) in
	      if le_test min max 
	      then Some ((min,max))
	      else None
	| _ -> None

(*
    let meet i1 i2 = 
      let res = meet i1 i2 in
	Printf.printf "%s meet %s = %s\n"
	  (to_string i1)(to_string i2)(to_string res); res
*)

    let widen i1 i2 =
      match (i1, i2) with
	| (Some i1, Some i2) ->
	    Some (((if le_test (min i1) (min i2) then (min i1) else Infty_neg),
		       (if le_test (max i2) (max i1) then (max i1) else Infty_pos)))
	| (None,i2) -> i2
	| (i1,None) -> i1

(*
    let widen i1 i2 =
      let w = widen i1 i2 in
	Printf.printf "%s W %s = %s\n"
	  (to_string i1) (to_string i2) (to_string w); w
*)
  
    let narrow i1 i2 =
      match (i1, i2) with
	| (Some i1, Some i2) ->
	    Some (((if min i1 = Infty_neg then min i2 else min i1),
		       (if max i1 = Infty_pos then max i2 else max i2)))
	| _ -> None

    let order_dec i1 i2 =
      match (i1, i2) with
	| (None, _) -> true
	| (Some i1, None) -> false
	| (Some i1, Some i2) ->
	    le_test (min i2) (min i1) && le_test (max i1) (max i2) 

    let bottom () = None

    let top () = Some ((Infty_neg, Infty_pos))

  end 

  let sub1 = function
    | Z a0 -> Z (Num.sub_num a0 (Num.num_of_int 1))
    | Infty_pos -> Infty_pos
    | Infty_neg -> Infty_neg

  let add1 = function
    | Z a0 -> Z (Num.add_num a0 (Num.num_of_int 1))
    | Infty_pos -> Infty_pos
    | Infty_neg -> Infty_neg
    
  let backward_eq n1 n2 =
    ((L.meet n1 n2), (L.meet n1 n2))
  
  let backward_lt n1 n2 =
    match n1 with
      | Some ((a, b)) ->
          (match n2 with
	     | Some ((c, d)) ->
                 (L.meet n1 (Some ((Infty_neg, sub1 d))),
                  L.meet n2 (Some ((add1 a, Infty_pos))))
             | None -> (None, None))
      | None -> (None, None)

  let backward_neq n1 n2 =
    let (n1',n2') = backward_lt n1 n2 in
    let (n1'',n2'') = backward_lt n2 n1 in
      (L.join n1' n1'',L.join n2' n2'')

  let backward_le n1 n2 =
    match n1 with
      | Some ((a, b)) ->
          (match n2 with
	     | Some ((c, d)) ->
                 (L.meet n1 (Some ((Infty_neg, d))),
                  L.meet n2 (Some ((a, Infty_pos))))
             | None -> (None, None))
      | None -> (None, None)

  let backward_comp = function
    | Eq -> backward_eq
    | Neq -> backward_neq
    | Lt -> backward_lt
    | Le -> backward_le
	
    
  let add' x y =
    match x with
      | Z a ->
          (match y with
             | Z b -> Z (Num.add_num a b) 
             | Infty_pos -> Infty_pos
             | Infty_neg -> Infty_neg)
      | Infty_pos -> Infty_pos
      | Infty_neg ->
          (match y with
             | Z z0 -> Infty_neg
             | Infty_pos -> Infty_pos
             | Infty_neg -> Infty_neg)
  
  let sub' x y =
    match x with
      | Z a ->
          (match y with
             | Z b -> Z (Num.sub_num a b)
             | Infty_pos -> Infty_neg
             | Infty_neg -> Infty_pos)
      | Infty_pos -> Infty_pos
      | Infty_neg -> Infty_neg  

  let mult' x y =
    match x with
      | Z a ->
          (match y with
             | Z b -> Z (Num.mult_num a b)
             | Infty_pos ->
		 if Num.eq_num a (Num.num_of_int 0) then Z (Num.num_of_int 0)
		 else if Num.lt_num a (Num.num_of_int 0) then Infty_neg
		 else Infty_pos
             | Infty_neg ->
		 if Num.eq_num a (Num.num_of_int 0) then Z (Num.num_of_int 0)
		 else if Num.lt_num a (Num.num_of_int 0) then Infty_pos
		 else Infty_neg)
      | Infty_pos ->
          (match y with
             | Z b ->
		 if Num.eq_num b (Num.num_of_int 0) then Z (Num.num_of_int 0)
		 else if Num.lt_num b (Num.num_of_int 0) then Infty_neg
		 else Infty_pos
             | Infty_pos -> Infty_pos
             | Infty_neg -> Infty_neg)
      | Infty_neg ->
          (match y with
             | Z b ->
		 if Num.eq_num b (Num.num_of_int 0) then Z (Num.num_of_int 0)
		 else if Num.lt_num b (Num.num_of_int 0) then Infty_pos
		 else Infty_neg
             | Infty_pos -> Infty_neg
             | Infty_neg -> Infty_pos)
    
  let forward_binop op i1 i2 =
      match (i1, i2) with
	| (Some (a,b), Some (c,d)) ->
	    (match op with
	       | Add -> Some (((add' a c),(add' b d)))
	       | Sub -> Some (((sub' a d),(sub' b c)))
	       | Mult -> 
		   let min4 i1 i2 i3 i4 =
		     min_z' (min_z' i1 i2) (min_z' i3 i4) in
		   let max4 i1 i2 i3 i4 =
		     max_z' (max_z' i1 i2) (max_z' i3 i4) in
		     Some ((min4 (mult' a c) (mult' a d) (mult' b c) (mult' b d),
				max4 (mult' a c) (mult' a d) (mult' b c) (mult' b d))))
	| _ -> None

  let reduce a b =
    if le_test a b then Some ((a, b)) else None

  let backward_binop op i1 i2 i3 =
    match (i1,i2,i3) with
      | (Some ((a,b)),Some ((c,d)),Some ((e,f))) ->
	  (match op with
	     | Add -> (reduce (max_z' c (sub' a f)) (min_z' d (sub' b e)),
		       reduce (max_z' e (sub' a d)) (min_z' f (sub' b c)))
	     | Sub -> (reduce (max_z' c (add' a e)) (min_z' d (add' b f)),
		       reduce (max_z' e (sub' c b)) (min_z' f (sub' d a)))
	     | Mult -> (Some ((c,d)),Some ((e,f))))
      | _ -> (None,None)
  
  let const n =
    Some (((Z (Num.num_of_int n)), (Z (Num.num_of_int n))))

end
