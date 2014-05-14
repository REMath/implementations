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

(** Control flow graph generation and manipulation *)

type instr = 
  | Assign of Syntax.var * Syntax.expr 
  | Assert of Syntax.test

(** entry label of statements *)
val entry : Syntax.stmt -> Syntax.label

(** [build p] returns the list of edges of the control flow graph of the program [p] *)
val build : Syntax.program -> (Syntax.label * instr * Syntax.label) list

(** [print_cfg p] prints the edges of the control flow graph o the program [p] on the standard output *)
val print_cfg : Syntax.program -> unit
