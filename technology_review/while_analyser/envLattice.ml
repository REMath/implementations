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

module Make =
  functor (L:Lattice.S) ->
struct
  
  module M = Map.Make(struct type t = string let compare = compare end)

  type t = L.t M.t
      
  let update env x v = M.add x v env
  let get env x = M.find x env

  let order_dec = M.equal L.order_dec
  
  let join x y =
    try
      M.mapi 
	(fun key v -> L.join v (M.find key y))
	x
    with Not_found -> assert false

  let meet x y =
    try
      M.mapi 
	(fun key v -> L.meet v (M.find key y))
	x
    with Not_found -> assert false

  let widen x y =
    try
      M.mapi 
	(fun key v -> L.widen v (M.find key y))
	x
    with Not_found -> assert false
    
  let narrow x y =
    try
      M.mapi 
	(fun key v -> L.narrow v (M.find key y))
	x
    with Not_found -> assert false
  
  let vars = ref ([]:string list)

  let init l_vars =
    vars := l_vars

  let bottom () =
    List.fold_right
      (fun key m -> M.add key (L.bottom ()) m)
      !vars
      M.empty

  let top () =
    List.fold_right
      (fun key m -> M.add key (L.top ()) m)
      !vars
      M.empty

  let to_string env =
    M.fold
      (fun key v s -> 
	 let x = L.to_string v in
	   if x = L.to_string (L.top ()) then s 
	   else Printf.sprintf "%s:%s  %s" key x s)
      env ""

end
  
