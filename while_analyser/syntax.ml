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

type label = int
type var = string

type binop =
  | Add | Sub | Mult

type expr =
  | Const of int
  | Unknown
  | Var of var
  | Binop of binop * expr * expr

type comp = Eq | Neq | Le | Lt

type test =
  | Comp of comp * expr * expr
  | And of test * test
  | Or of test * test

type stmt =
  | Assign of label * var * expr
  | Skip of label
  | If of label * test * stmt * stmt
  | While of label * test *stmt
  | Seq of stmt * stmt

type program = stmt * label

(*********************************************************)
(* Computes of the set of variables present in a program *)
(*********************************************************)

module S = Set.Make (struct type t = var let compare = compare end)

let rec var_expr s = function
  | Const z -> s
  | Unknown -> s
  | Var x -> S.add x s
  | Binop (o,e1,e2) -> var_expr (var_expr s e1) e2

let rec var_test s = function
  | Comp (c,e1,e2) -> var_expr (var_expr s e1) e2
  | And (t1,t2) -> var_test (var_test s t1) t2
  | Or (t1,t2) -> var_test (var_test s t1) t2

let rec var_stmt s = function
  | Skip l -> s
  | Assign (l,x,e) -> S.add x (var_expr s e)
  | If (l,t,b1,b2) -> var_test (var_stmt (var_stmt s b1) b2) t
  | While (l,t,b) -> var_test (var_stmt s b) t
  | Seq (i1,i2) -> var_stmt (var_stmt s i1) i2

let vars (p,l) = S.elements (var_stmt S.empty p)
