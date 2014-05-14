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

(** The interfaces of abstractions *)

(** numeric abstraction of integers *)
module type Num = 
sig
  module L : Lattice.S

  val backward_comp : Syntax.comp -> L.t -> L.t -> (L.t * L.t)

  val forward_binop : Syntax.binop -> L.t -> L.t -> L.t  

  val backward_binop : Syntax.binop -> L.t -> L.t -> L.t -> L.t * L.t

  val const : int -> L.t
end

(** numeric abstraction of environments *)
module type Env =  
sig 
  module L : Lattice.S

  val init : Syntax.var list -> unit
    
  val init_env : unit -> L.t

  val assign : Syntax.var -> Syntax.expr -> L.t -> L.t
        
  val backward_test : Syntax.test -> L.t -> L.t
end



