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

(** The lattice signature *)

module type S = 
sig 
  (** the type of the elements of the lattice *)
  type t 

  (** partial order boolean test *)
  val order_dec : t -> t -> bool

  (** lattice binary least upper bound *)
  val join : t -> t -> t

  (** lattice binary greates lower bound *)
  val meet : t -> t -> t

  (** widening operator *)
  val widen : t -> t -> t

  (** narrowing operator *)
  val narrow : t -> t -> t

  (** [bottom ()] returns the least element of the lattice *)
  val bottom : unit -> t

  (** [top ()] returns the greates element of the lattice *)
  val top : unit -> t

  (** string representation of the lattice elements *)
  val to_string : t -> string
end
