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

open Printf
open Syntax

let print_op = function
  | Add -> "+"
  | Sub -> "-"
  | Mult -> "*"
      
type symb = No | Plus | Opp | Mul

let rec print_expr tab priop first scal_optim = function
  | Const z -> string_of_int z
  | Unknown -> "?"
  | Var x -> tab x
  | Binop (Sub,e,Const i) when i=0  -> 
      if priop = No || priop = Opp || first then sprintf "-%s" (print_expr tab Opp false scal_optim e)
      else  sprintf "(-%s)" (print_expr tab Opp false scal_optim e)
  | Binop (Mult,Const z,Var x) when scal_optim ->
      sprintf "%d%s" z (tab x)
  | Binop (Mult,e1,e2)  -> sprintf "%s * %s" (print_expr tab Mul first scal_optim e1) (print_expr tab Mul false scal_optim e2)
  | Binop (Add,e1,e2)  -> 
      if priop = Mul || priop = Opp then sprintf "(%s + %s)" (print_expr tab Plus first scal_optim e1) (print_expr tab Plus false scal_optim e2)
      else sprintf "%s + %s" (print_expr tab Plus first scal_optim e1) (print_expr tab Plus false scal_optim e2)
  | Binop (Sub,e1,e2)  -> 
      if priop = Mul || priop = Opp then sprintf "(%s - %s)" (print_expr tab Plus first scal_optim e1) (print_expr tab Opp false scal_optim e2)
      else sprintf "%s - %s" (print_expr tab Plus first scal_optim e1) (print_expr tab Opp false scal_optim e2)

let print_comp eq = function
  | Eq -> eq
  | Neq -> "<>"
  | Lt -> "<"
  | Le -> "<="

type prioptest = PAnd | PNo

let rec print_test_aux print_comp tab filter sor sand eq priop scal_optim = function
    (*    | Not t -> "not "^(print_test tab t) *)
  | Comp (c,e1,e2) -> filter (sprintf "%s %s %s" (print_expr tab No true scal_optim e1) (print_comp eq c) (print_expr tab No true scal_optim e2))
  | And (t1,t2) -> 
      let s = sprintf "%s %s %s" (print_test_aux print_comp tab filter sor sand eq PAnd scal_optim t1) sand (print_test_aux print_comp tab filter sor sand eq PAnd scal_optim t2) in
	if priop = PAnd then s else sprintf "(%s)" s 
  | Or (t1,t2) -> sprintf "(%s %s %s)" (print_test_aux print_comp tab filter sor sand eq PNo scal_optim t1) sor (print_test_aux print_comp tab filter sor sand eq PNo scal_optim t2) 

let print_test tab = print_test_aux print_comp tab (fun x -> x) "or" "and" "==" PNo false

let filter_top_bot = function
  | "0 = 1" -> "False"
  | "0 = 0" -> "True"
  | x -> x
let print_test_symb tab = print_test_aux  print_comp tab filter_top_bot "\\/" "/\\" "=" PAnd true

let print_test_coq tab = print_test_aux  print_comp tab filter_top_bot "\\/" "/\\" "=" PAnd false

let print_comp_latex eq = function
  | Eq -> eq
  | Neq -> "\\not="
  | Lt -> "<"
  | Le -> "\\leq"

let print_test_latex tab = print_test_aux print_comp_latex tab filter_top_bot "\\lor" "\\land" "=" PAnd false

let print_res f idt p  =
  sprintf "                                      // %s\n" (f p) 

let print_pp idt = sprintf "(%d) "

let ident = "  "

let rec print_instr tab f idt end_block = function
(*  | Assert t -> sprintf "assert (%s)"  (print_test tab t)
  | Ensure t -> sprintf "ensure (%s)"  (print_test tab t) *)
  | Skip l -> sprintf "%s%sskip%s" (f idt l) idt end_block
  | Assign (l,x,e) -> sprintf "%s%s%s = %s%s" (f idt l) idt (tab x) (print_expr tab No true false e) end_block
  | If (l,t,b1,b2) -> let pt = print_test tab t in
      sprintf "%s%sif %s {\n%s%s} else {\n%s%s}%s" (f idt l) idt
        pt (print_instr tab f (idt^ident) "\n" b1) idt
        (print_instr tab f (idt^ident) "\n" b2) idt
	end_block
  | While (l,t,b)  -> let pt = print_test tab t in
      sprintf "%s%swhile %s {\n%s%s}%s" (f idt l) idt pt
        (print_instr tab f (idt^ident) "\n" b) idt end_block
  | Seq (i1,i2) -> sprintf "%s;\n%s" (print_instr tab f idt "" i1) (print_instr tab f idt end_block i2)

let print_expr = print_expr (fun x -> x) No true false

let print_test = print_test (fun x -> x)

let print_program f (p,l) = 
  sprintf "%s\n%s\n"
    (print_instr (fun x -> x) f "" "" p) 
    (f "" l)

let print_program_with_res p res = print_program (print_res res) p

let print_program = print_program print_pp

