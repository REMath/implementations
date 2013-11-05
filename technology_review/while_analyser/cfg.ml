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

type instr =
  | Assign of var * expr
  | Assert of test

module S = Set.Make (struct type t = label * instr * label let compare = compare end)

let rec entry = function
  | Syntax.Assign (l,x,e) -> l
  | Skip l -> l
  | If (l,t,i1,i2) -> l
  | While (l,t,i)  -> l
  | Seq (i1,i2) -> entry i1

let neg_comp = function
  | Eq -> Neq
  | Neq -> Eq
  | Le -> Lt
  | Lt -> Le

let rec neg_test = function
  | Comp (c,e1,e2) -> Comp (neg_comp c,e2,e1)
  | And (t1,t2) -> Or (neg_test t1,neg_test t2)
  | Or (t1,t2) -> And (neg_test t1,neg_test t2)

let rec cfg end_label = function
  | Syntax.Assign (l,x,e) -> S.add (l,Assign (x,e),end_label) S.empty
  | Skip l -> S.add (l,Assert (Comp (Eq,Const 0,Const 0)),end_label) S.empty
  | If (l,t,i1,i2) -> 
      S.add (l,Assert t,entry i1) 
	(S.add (l,Assert (neg_test t),entry i2)  
	   (S.union (cfg end_label i1) (cfg end_label i2)))
  | While (l,t,i)  ->
      S.add (l,Assert t,entry i) 
	(S.add (l,Assert (neg_test t),end_label) (cfg l i))
  | Seq (i1,i2) -> S.union (cfg (entry i2) i1) (cfg end_label i2)

let build (p,l) = S.elements (cfg l p)

let print_cfg p =
  List.iter
    (fun (l1,i,l2) ->
       Printf.printf "%d --[%s]--> %d\n" 
	 l1
	 (match i with
	    | Assign (x,e) -> Printf.sprintf "%s := %s" x ((Print.print_expr e))
	    | Assert t -> Print.print_test t
	 )
	 l2)
    (build p)

