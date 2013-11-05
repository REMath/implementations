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

(** The lattice of abstract environment ordered with a point-wise partial order *)

module Make :
  functor (L : Lattice.S) ->
    sig
      module M : Map.S with type key = Syntax.var
      type t = L.t M.t

	  (** [update env x v] updates the abstract environment [env] with the variable [x] binded with the abstract value [v] *)
      val update : t -> M.key -> L.t -> t

	  (** [get env x] returns the abstract value binded with the variable [x] *)
      val get : t -> M.key -> L.t

      val order_dec : L.t M.t -> L.t M.t -> bool
      val join : L.t M.t -> L.t M.t -> L.t M.t
      val meet : L.t M.t -> L.t M.t -> L.t M.t
      val widen : L.t M.t -> L.t M.t -> L.t M.t
      val narrow : L.t M.t -> L.t M.t -> L.t M.t
      val vars : M.key list ref
      val init : M.key list -> unit
      val bottom : unit -> L.t M.t
      val top : unit -> L.t M.t
      val to_string : L.t M.t -> string
    end
