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
struct
  module L =
  struct

  type t =
    | Bot
    | Top
    | Pos
    | Neg
    | Zero
    | Pos0
    | Neg0
  
  let order_dec x y =
    match x with
      | Bot -> true
      | Top -> y=Top
      | Pos -> 
          (match y with
             | Top | Pos | Pos0 -> true
             | _ -> false)
      | Neg ->
          (match y with
             | Top | Neg | Neg0 -> true
             | _ -> false)
      | Zero ->
	  (match y with
	     | Bot | Neg | Pos -> false
             | _ -> true)
      | Pos0 ->
	  (match y with
	     | Top | Pos0 -> true
             | _ -> false)
      | Neg0 ->
          (match y with
	     | Top | Neg0 -> true
             | _ -> false)
  
  let join x y =
    match x with
      | Bot -> y
      | Top -> Top
      | Pos -> 
          (match y with
             | Bot -> x
             | Top -> Top
             | Pos -> Pos
             | Neg -> Top
             | Zero -> Pos0
             | Pos0 -> Pos0
             | Neg0 -> Top)
      | Neg ->
          (match y with
             | Bot -> x
             | Top -> Top
             | Pos -> Top
             | Neg -> Neg
             | Zero -> Neg0
             | Pos0 -> Top
             | Neg0 -> Neg0)
      | Zero ->
          (match y with
             | Bot -> x
             | Top -> Top
             | Pos -> Pos0
             | Neg -> Neg0
             | Zero -> Zero
             | Pos0 -> Pos0
             | Neg0 -> Neg0)
      | Pos0 ->
          (match y with
             | Bot -> x
             | Top -> Top
             | Pos -> Pos0
             | Neg -> Top
             | Zero -> Pos0
             | Pos0 -> Pos0
             | Neg0 -> Top)
      | Neg0 ->
          (match y with
             | Bot -> x
             | Top -> Top
             | Pos -> Top
             | Neg -> Neg0
             | Zero -> Neg0
             | Pos0 -> Top
             | Neg0 -> Neg0)
  
  let meet x y =
    match x with
      | Bot -> Bot
      | Top -> y
      | Pos ->
          (match y with
             | Bot -> Bot
             | Top -> x
             | Pos -> Pos
             | Neg -> Bot
             | Zero -> Bot
             | Pos0 -> Pos
             | Neg0 -> Bot)
      | Neg ->
          (match y with
             | Bot -> Bot
             | Top -> x
             | Pos -> Bot
             | Neg -> Neg
             | Zero -> Bot
             | Pos0 -> Bot
             | Neg0 -> Neg)
      | Zero ->
          (match y with
             | Bot -> Bot
             | Top -> x
             | Pos -> Bot
             | Neg -> Bot
             | Zero -> Zero
             | Pos0 -> Zero
             | Neg0 -> Zero)
      | Pos0 ->
          (match y with
             | Bot -> Bot
             | Top -> x
             | Pos -> Pos
             | Neg -> Bot
             | Zero -> Zero
             | Pos0 -> Pos0
             | Neg0 -> Zero)
      | Neg0 ->
          (match y with
             | Bot -> Bot
             | Top -> x
             | Pos -> Bot
             | Neg -> Neg
             | Zero -> Zero
             | Pos0 -> Zero
             | Neg0 -> Neg0)
  
  let widen = join
  let narrow x y = x
  
  let bottom () = Bot

  let top () = Top

  let to_string = function
    | Bot -> "bot"
    | Top -> "top"
    | Pos -> "+"
    | Neg -> "-"
    | Zero -> "0"
    | Pos0 -> "+,0"
    | Neg0 -> "-,0" 

 end 
 
  let backward_eq n1 n2 =
    ((L.meet n1 n2), (L.meet n1 n2))
  
  let backward_neq n1 n2 =
    match n1 with
      | L.Bot -> (L.Bot, L.Bot)
      | L.Top -> (n1,n2)
      | L.Pos ->
          (match n2 with
             | L.Bot -> (L.Bot, L.Bot)
             | _ -> (n1, n2))
      | L.Neg ->
          (match n2 with
             | L.Bot -> (L.Bot, L.Bot)
             | _ -> (n1, n2))
      | L.Zero ->
          (match n2 with
             | L.Bot -> (L.Bot, L.Bot)
             | L.Zero -> (L.Bot, L.Bot)
             | L.Pos0 -> (L.Zero, L.Pos)
             | L.Neg0 -> (L.Zero, L.Neg)
             | _ -> (n1, n2))
      | L.Pos0 ->
          (match n2 with
             | L.Bot -> (L.Bot, L.Bot)
             | L.Zero -> (L.Pos, L.Zero)
             | _ -> (n1, n2))
      | L.Neg0 ->
          (match n2 with
             | L.Bot -> (L.Bot, L.Bot)
             | L.Zero -> (L.Neg, L.Zero)
             | _ -> (n1, n2))

  let backward_lt n1 n2 =
    match n1 with
      | L.Bot -> (L.Bot, L.Bot)
      | L.Top ->
          (match n2 with
             | L.Bot -> (L.Bot, L.Bot)
             | L.Top -> (n1, n2)
             | L.Pos -> (n1, n2)
             | L.Neg -> (L.Neg, L.Neg)
             | L.Zero -> (L.Neg, L.Zero)
             | L.Pos0 -> (n1, n2)
             | L.Neg0 -> (L.Neg, L.Neg0))
      | L.Pos ->
          (match n2 with
             | L.Bot -> (L.Bot, L.Bot)
             | L.Top -> (L.Pos, L.Pos)
             | L.Pos -> (n1, n2)
             | L.Neg -> (L.Bot, L.Bot)
             | L.Zero -> (L.Bot, L.Bot)
             | L.Pos0 -> (L.Pos, L.Pos)
             | L.Neg0 -> (L.Bot, L.Bot))
      | L.Neg ->
          (match n2 with
             | L.Bot -> (L.Bot, L.Bot)
             | L.Top -> (n1, n2)
             | L.Pos -> (n1, n2)
             | L.Neg -> (n1, n2)
             | L.Zero -> (n1, n2)
             | L.Pos0 -> (n1, n2)
             | L.Neg0 -> (n1, n2))
      | L.Zero ->
          (match n2 with
             | L.Bot -> (L.Bot, L.Bot)
             | L.Top -> (L.Zero, L.Pos)
             | L.Pos -> (n1, n2)
             | L.Neg -> (L.Bot, L.Bot)
             | L.Zero -> (L.Bot, L.Bot)
             | L.Pos0 -> (L.Zero, L.Pos)
             | L.Neg0 -> (L.Bot, L.Bot))
      | L.Pos0 ->
          (match n2 with
             | L.Bot -> (L.Bot, L.Bot)
             | L.Top -> (L.Pos0, L.Pos)
             | L.Pos -> (L.Pos0, L.Pos)
             | L.Neg -> (L.Bot, L.Bot)
             | L.Zero -> (L.Bot, L.Bot)
             | L.Pos0 -> (L.Pos0, L.Pos)
             | L.Neg0 -> (L.Bot, L.Bot))
      | L.Neg0 ->
          (match n2 with
             | L.Bot -> (L.Bot, L.Bot)
             | L.Top -> (n1, n2)
             | L.Pos -> (n1, n2)
             | L.Neg -> (L.Neg, L.Neg)
             | L.Zero -> (L.Neg, L.Zero)
             | L.Pos0 -> (n1, n2)
             | L.Neg0 -> (L.Neg, L.Neg0))

  let backward_le n1 n2 =
    match n1 with
      | L.Bot -> (L.Bot, L.Bot)
      | L.Top ->
          (match n2 with
             | L.Bot -> (L.Bot, L.Bot)
             | L.Top -> (n1, n2)
             | L.Pos -> (n1, n2)
             | L.Neg -> (L.Neg, L.Neg)
             | L.Zero -> (L.Neg0, L.Zero)
             | L.Pos0 -> (n1, n2)
             | L.Neg0 -> (L.Neg0, L.Neg0))
      | L.Pos ->
          (match n2 with
             | L.Bot -> (L.Bot, L.Bot)
             | L.Top -> (L.Pos, L.Pos)
             | L.Pos -> (n1, n2)
             | L.Neg -> (L.Bot, L.Bot)
             | L.Zero -> (L.Bot, L.Bot)
             | L.Pos0 -> (L.Pos, L.Pos)
             | L.Neg0 -> (L.Bot, L.Bot))
      | L.Neg ->
          (match n2 with
             | L.Bot -> (L.Bot, L.Bot)
             | L.Top -> (n1, n2)
             | L.Pos -> (n1, n2)
             | L.Neg -> (n1, n2)
             | L.Zero -> (n1, n2)
             | L.Pos0 -> (n1, n2)
             | L.Neg0 -> (n1, n2))
      | L.Zero ->
          (match n2 with
             | L.Bot -> (L.Bot, L.Bot)
             | L.Top -> (L.Zero, L.Pos0)
             | L.Pos -> (n1, n2)
             | L.Neg -> (L.Bot, L.Bot)
             | L.Zero -> (n1, n2)
             | L.Pos0 -> (n1, n2)
             | L.Neg0 -> (L.Bot, L.Bot))
      | L.Pos0 ->
          (match n2 with
             | L.Bot -> (L.Bot, L.Bot)
             | L.Top -> (L.Pos0, L.Pos0)
             | L.Pos -> (L.Pos0, L.Pos)
             | L.Neg -> (L.Bot, L.Bot)
             | L.Zero -> (L.Bot, L.Bot)
             | L.Pos0 -> (L.Pos0, L.Pos0)
             | L.Neg0 -> (L.Bot, L.Bot))
      | L.Neg0 ->
          (match n2 with
             | L.Bot -> (L.Bot, L.Bot)
             | L.Top -> (n1, n2)
             | L.Pos -> (n1, n2)
             | L.Neg -> (L.Neg, L.Neg)
             | L.Zero -> (n1, n2)
             | L.Pos0 -> (n1, n2)
             | L.Neg0 -> (n1, n2))

  let forward_add n1 n2 =
    match n1 with
      | L.Bot -> L.Bot
      | L.Top ->
          (match n2 with
             | L.Bot -> L.Bot
             | L.Top -> L.Top
             | L.Pos -> L.Top
             | L.Neg -> L.Top
             | L.Zero -> n1
             | L.Pos0 -> L.Top
             | L.Neg0 -> L.Top)
      | L.Pos ->
          (match n2 with
             | L.Bot -> L.Bot
             | L.Top -> L.Top
             | L.Pos -> L.Pos
             | L.Neg -> L.Top
             | L.Zero -> n1
             | L.Pos0 -> L.Pos
             | L.Neg0 -> L.Top)
      | L.Neg ->
          (match n2 with
             | L.Bot -> L.Bot
             | L.Top -> L.Top
             | L.Pos -> L.Top
             | L.Neg -> L.Neg
             | L.Zero -> n1
             | L.Pos0 -> L.Top
             | L.Neg0 -> L.Neg)
      | L.Zero ->
          (match n2 with
             | L.Bot -> L.Bot
             | L.Top -> n2
             | L.Pos -> n2
             | L.Neg -> n2
             | L.Zero -> n2
             | L.Pos0 -> n2
             | L.Neg0 -> n2)
      | L.Pos0 ->
          (match n2 with
             | L.Bot -> L.Bot
             | L.Top -> L.Top
             | L.Pos -> L.Pos
             | L.Neg -> L.Top
             | L.Zero -> n1
             | L.Pos0 -> L.Pos0
             | L.Neg0 -> L.Top)
      | L.Neg0 ->
          (match n2 with
             | L.Bot -> L.Bot
             | L.Top -> L.Top
             | L.Pos -> L.Top
             | L.Neg -> L.Neg
             | L.Zero -> n1
             | L.Pos0 -> L.Top
             | L.Neg0 -> L.Neg0)
  
  let forward_sub n1 n2 =
    match n1 with
      | L.Bot -> L.Bot
      | L.Top ->
          (match n2 with
             | L.Bot -> L.Bot
             | L.Top -> L.Top
             | L.Pos -> L.Top
             | L.Neg -> L.Top
             | L.Zero -> n1
             | L.Pos0 -> L.Top
             | L.Neg0 -> L.Top)
      | L.Pos ->
          (match n2 with
             | L.Bot -> L.Bot
             | L.Top -> L.Top
             | L.Pos -> L.Top
             | L.Neg -> L.Pos
             | L.Zero -> n1
             | L.Pos0 -> L.Top
             | L.Neg0 -> L.Pos)
      | L.Neg ->
          (match n2 with
             | L.Bot -> L.Bot
             | L.Top -> L.Top
             | L.Pos -> L.Neg
             | L.Neg -> L.Top
             | L.Zero -> n1
             | L.Pos0 -> L.Neg
             | L.Neg0 -> L.Top)
      | L.Zero -> 
          (match n2 with
             | L.Bot -> L.Bot
             | L.Top -> L.Top
             | L.Pos -> L.Neg
             | L.Neg -> L.Pos
             | L.Zero -> n1
             | L.Pos0 -> L.Neg0
             | L.Neg0 -> L.Pos0)
      | L.Pos0 ->
          (match n2 with
             | L.Bot -> L.Bot
             | L.Top -> L.Top
             | L.Pos -> L.Top
             | L.Neg -> L.Pos
             | L.Zero -> n1
             | L.Pos0 -> L.Top
             | L.Neg0 -> L.Pos0)
      | L.Neg0 ->
          (match n2 with
             | L.Bot -> L.Bot
             | L.Top -> L.Top
             | L.Pos -> L.Neg
             | L.Neg -> L.Top
             | L.Zero -> n1
             | L.Pos0 -> L.Neg0
             | L.Neg0 -> L.Top)
  
  let forward_mult n1 n2 =
    match n1 with
      | L.Bot -> L.Bot
      | L.Top ->
          (match n2 with
             | L.Bot -> L.Bot
             | L.Top -> L.Top
             | L.Pos -> L.Top
             | L.Neg -> L.Top
             | L.Zero -> L.Zero
             | L.Pos0 -> L.Top
             | L.Neg0 -> L.Top)
      | L.Pos ->
          (match n2 with
             | L.Bot -> L.Bot
             | L.Top -> L.Top
             | L.Pos -> L.Pos
             | L.Neg -> L.Neg
             | L.Zero -> L.Zero
             | L.Pos0 -> L.Pos0
             | L.Neg0 -> L.Top)
      | L.Neg ->
          (match n2 with
             | L.Bot -> L.Bot
             | L.Top -> L.Top
             | L.Pos -> L.Neg
             | L.Neg -> L.Pos
             | L.Zero -> L.Zero
             | L.Pos0 -> L.Top
             | L.Neg0 -> L.Pos0)
      | L.Zero ->
          (match n2 with
             | L.Bot -> L.Bot
             | L.Top -> L.Zero
             | L.Pos -> L.Zero
             | L.Neg -> L.Zero
             | L.Zero -> L.Zero
             | L.Pos0 -> L.Zero
             | L.Neg0 -> L.Zero)
      | L.Pos0 ->
          (match n2 with
             | L.Bot -> L.Bot
             | L.Top -> L.Top
             | L.Pos -> L.Pos0
             | L.Neg -> L.Top
             | L.Zero -> L.Zero
             | L.Pos0 -> L.Pos0
             | L.Neg0 -> L.Top)
      | L.Neg0 ->
          (match n2 with
             | L.Bot -> L.Bot
             | L.Top -> L.Top
             | L.Pos -> L.Top
             | L.Neg -> L.Pos0
             | L.Zero -> L.Zero
             | L.Pos0 -> L.Top
             | L.Neg0 -> L.Pos0)
  
  let backward_add n n1 n2 =
    match n with
      | L.Bot -> (L.Bot, L.Bot)
      | L.Top ->
          (match n1 with
             | L.Bot -> (L.Bot, L.Bot)
             | L.Top ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Pos ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Neg ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Zero ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Pos0 ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Neg0 ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2)))
      | L.Pos ->
          (match n1 with
             | L.Bot -> (L.Bot, L.Bot)
             | L.Top ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (L.Pos, L.Neg)
                    | L.Zero -> (L.Pos, L.Zero)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Pos ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Neg ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (L.Neg, L.Pos)
                    | L.Pos -> (L.Neg, L.Pos)
                    | L.Neg -> (L.Bot, L.Bot)
                    | L.Zero -> (L.Bot, L.Bot)
                    | L.Pos0 -> (L.Neg, L.Pos)
                    | L.Neg0 -> (L.Bot, L.Bot))
             | L.Zero ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (L.Zero, L.Pos)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (L.Bot, L.Bot)
                    | L.Zero -> (L.Bot, L.Bot)
                    | L.Pos0 -> (L.Zero, L.Pos)
                    | L.Neg0 -> (L.Bot, L.Bot))
             | L.Pos0 ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (L.Pos, L.Neg)
                    | L.Zero -> (L.Pos, L.Zero)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Neg0 ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (L.Neg0, L.Pos)
                    | L.Pos -> (L.Neg0, L.Pos)
                    | L.Neg -> (L.Bot, L.Bot)
                    | L.Zero -> (L.Bot, L.Bot)
                    | L.Pos0 -> (L.Neg0, L.Pos)
                    | L.Neg0 -> (L.Bot, L.Bot)))
      | L.Neg ->
          (match n1 with
             | L.Bot -> (L.Bot, L.Bot)
             | L.Top ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (L.Neg, L.Pos)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (L.Neg, L.Zero)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Pos ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (L.Pos, L.Neg)
                    | L.Pos -> (L.Bot, L.Bot)
                    | L.Neg -> (L.Pos, L.Neg)
                    | L.Zero -> (L.Bot, L.Bot)
                    | L.Pos0 -> (L.Bot, L.Bot)
                    | L.Neg0 -> (L.Pos, L.Neg))
             | L.Neg ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Zero ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (L.Zero, L.Neg)
                    | L.Pos -> (L.Bot, L.Bot)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (L.Bot, L.Bot)
                    | L.Pos0 -> (L.Bot, L.Bot)
                    | L.Neg0 -> (L.Zero, L.Neg))
             | L.Pos0 ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (L.Pos0, L.Neg)
                    | L.Pos -> (L.Bot, L.Bot)
                    | L.Neg -> (L.Pos0, L.Neg)
                    | L.Zero -> (L.Bot, L.Bot)
                    | L.Pos0 -> (L.Bot, L.Bot)
                    | L.Neg0 -> (L.Pos0, L.Neg))
             | L.Neg0 ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (L.Neg, L.Pos)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (L.Neg, L.Zero)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2)))
      | L.Zero ->
          (match n1 with
             | L.Bot -> (L.Bot, L.Bot)
             | L.Top ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (L.Neg, L.Pos)
                    | L.Neg -> (L.Pos, L.Neg)
                    | L.Zero -> (L.Zero, L.Zero)
                    | L.Pos0 -> (L.Neg0, L.Pos0)
                    | L.Neg0 -> (L.Pos0, L.Neg0))
             | L.Pos ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (L.Pos, L.Neg)
                    | L.Pos -> (L.Bot, L.Bot)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (L.Bot, L.Bot)
                    | L.Pos0 -> (L.Bot, L.Bot)
                    | L.Neg0 -> (L.Pos, L.Neg))
             | L.Neg ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (L.Neg, L.Pos)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (L.Bot, L.Bot)
                    | L.Zero -> (L.Bot, L.Bot)
                    | L.Pos0 -> (L.Neg, L.Pos)
                    | L.Neg0 -> (L.Bot, L.Bot))
             | L.Zero ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (L.Zero, L.Zero)
                    | L.Pos -> (L.Bot, L.Bot)
                    | L.Neg -> (L.Bot, L.Bot)
                    | L.Zero -> (L.Zero, L.Zero)
                    | L.Pos0 -> (L.Zero, L.Zero)
                    | L.Neg0 -> (L.Zero, L.Zero))
             | L.Pos0 ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (L.Pos0, L.Neg0)
                    | L.Pos -> (L.Bot, L.Bot)
                    | L.Neg -> (L.Pos, L.Neg)
                    | L.Zero -> (L.Zero, L.Zero)
                    | L.Pos0 -> (L.Zero, L.Zero)
                    | L.Neg0 -> (n1, n2))
             | L.Neg0 ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (L.Neg0, L.Pos0)
                    | L.Pos -> (L.Neg, L.Pos)
                    | L.Neg -> (L.Bot, L.Bot)
                    | L.Zero -> (L.Zero, L.Zero)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (L.Zero, L.Zero)))
      | L.Pos0 ->
          (match n1 with
             | L.Bot -> (L.Bot, L.Bot)
             | L.Top ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Pos ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Neg ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Zero ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Pos0 ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Neg0 ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2)))
      | L.Neg0 ->
          (match n1 with
             | L.Bot -> (L.Bot, L.Bot)
             | L.Top ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Pos ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Neg ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Zero ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Pos0 ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Neg0 ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2)))
  
  let backward_sub n n1 n2 =
    match n with
      | L.Bot -> (L.Bot, L.Bot)
      | L.Top ->
          (match n1 with
             | L.Bot -> (L.Bot, L.Bot)
             | L.Top ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Pos ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Neg ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Zero ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Pos0 ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Neg0 ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2)))
      | L.Pos ->
          (match n1 with
             | L.Bot -> (L.Bot, L.Bot)
             | L.Top ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (L.Pos, L.Pos)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (L.Pos, L.Zero)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Pos ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Neg ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (L.Neg, L.Neg)
                    | L.Pos -> (L.Bot, L.Bot)
                    | L.Neg -> (L.Neg, L.Neg)
                    | L.Zero -> (L.Bot, L.Bot)
                    | L.Pos0 -> (L.Bot, L.Bot)
                    | L.Neg0 -> (L.Neg, L.Neg))
             | L.Zero ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (L.Zero, L.Neg)
                    | L.Pos -> (L.Bot, L.Bot)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (L.Bot, L.Bot)
                    | L.Pos0 -> (L.Bot, L.Bot)
                    | L.Neg0 -> (L.Zero, L.Neg))
             | L.Pos0 ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (L.Pos, L.Pos)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (L.Pos, L.Zero)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Neg0 ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (L.Neg0, L.Neg)
                    | L.Pos -> (L.Bot, L.Bot)
                    | L.Neg -> (L.Neg0, L.Neg)
                    | L.Zero -> (L.Bot, L.Bot)
                    | L.Pos0 -> (L.Bot, L.Bot)
                    | L.Neg0 -> (L.Neg0, L.Neg)))
      | L.Neg ->
          (match n1 with
             | L.Bot -> (L.Bot, L.Bot)
             | L.Top ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (L.Neg, L.Neg)
                    | L.Zero -> (L.Neg, L.Zero)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Pos ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (L.Pos, L.Pos)
                    | L.Pos -> (L.Pos, L.Pos)
                    | L.Neg -> (L.Bot, L.Bot)
                    | L.Zero -> (L.Bot, L.Bot)
                    | L.Pos0 -> (L.Pos, L.Pos)
                    | L.Neg0 -> (L.Bot, L.Bot))
             | L.Neg ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Zero ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (L.Zero, L.Pos)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (L.Bot, L.Bot)
                    | L.Zero -> (L.Bot, L.Bot)
                    | L.Pos0 -> (L.Zero, L.Pos)
                    | L.Neg0 -> (L.Bot, L.Bot))
             | L.Pos0 ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (L.Pos0, L.Pos)
                    | L.Pos -> (L.Pos0, L.Pos)
                    | L.Neg -> (L.Bot, L.Bot)
                    | L.Zero -> (L.Bot, L.Bot)
                    | L.Pos0 -> (L.Pos0, L.Pos)
                    | L.Neg0 -> (L.Bot, L.Bot))
             | L.Neg0 ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (L.Neg, L.Neg)
                    | L.Zero -> (L.Neg, L.Zero)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2)))
      | L.Zero ->
          (match n1 with
             | L.Bot -> (L.Bot, L.Bot)
             | L.Top ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (L.Pos, L.Pos)
                    | L.Neg -> (L.Neg, L.Neg)
                    | L.Zero -> (L.Zero, L.Zero)
                    | L.Pos0 -> (L.Pos0, L.Pos0)
                    | L.Neg0 -> (L.Neg0, L.Neg0))
             | L.Pos ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (L.Pos, L.Pos)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (L.Bot, L.Bot)
                    | L.Zero -> (L.Bot, L.Bot)
                    | L.Pos0 -> (L.Pos, L.Pos)
                    | L.Neg0 -> (L.Bot, L.Bot))
             | L.Neg ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (L.Neg, L.Neg)
                    | L.Pos -> (L.Bot, L.Bot)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (L.Bot, L.Bot)
                    | L.Pos0 -> (L.Bot, L.Bot)
                    | L.Neg0 -> (L.Neg, L.Neg))
             | L.Zero ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (L.Zero, L.Zero)
                    | L.Pos -> (L.Bot, L.Bot)
                    | L.Neg -> (L.Bot, L.Bot)
                    | L.Zero -> (L.Zero, L.Zero)
                    | L.Pos0 -> (L.Zero, L.Zero)
                    | L.Neg0 -> (L.Zero, L.Zero))
             | L.Pos0 ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (L.Pos0, L.Pos0)
                    | L.Pos -> (L.Pos, L.Pos)
                    | L.Neg -> (L.Bot, L.Bot)
                    | L.Zero -> (L.Zero, L.Zero)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (L.Zero, L.Zero))
             | L.Neg0 ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (L.Neg0, L.Neg0)
                    | L.Pos -> (L.Bot, L.Bot)
                    | L.Neg -> (L.Neg, L.Neg)
                    | L.Zero -> (L.Zero, L.Zero)
                    | L.Pos0 -> (L.Zero, L.Zero)
                    | L.Neg0 -> (n1, n2)))
      | L.Pos0 ->
          (match n1 with
             | L.Bot -> (L.Bot, L.Bot)
             | L.Top ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Pos ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Neg ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Zero ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Pos0 ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Neg0 ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2)))
      | L.Neg0 ->
          (match n1 with
             | L.Bot -> (L.Bot, L.Bot)
             | L.Top ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Pos ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Neg ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Zero ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Pos0 ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Neg0 ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2)))
  
  let backward_mult n n1 n2 =
    match n with
      | L.Bot -> (L.Bot, L.Bot)
      | L.Top ->
          (match n1 with
             | L.Bot -> (L.Bot, L.Bot)
             | L.Top ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Pos ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Neg ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Zero ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Pos0 ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Neg0 ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2)))
      | L.Pos ->
          (match n1 with
             | L.Bot -> (L.Bot, L.Bot)
             | L.Top ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (L.Pos, L.Pos)
                    | L.Neg -> (L.Neg, L.Neg)
                    | L.Zero -> (L.Bot, L.Bot)
                    | L.Pos0 -> (L.Pos, L.Pos)
                    | L.Neg0 -> (L.Neg, L.Neg))
             | L.Pos ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (L.Pos, L.Pos)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (L.Bot, L.Bot)
                    | L.Zero -> (L.Bot, L.Bot)
                    | L.Pos0 -> (L.Pos, L.Pos)
                    | L.Neg0 -> (L.Bot, L.Bot))
             | L.Neg ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (L.Neg, L.Neg)
                    | L.Pos -> (L.Bot, L.Bot)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (L.Bot, L.Bot)
                    | L.Pos0 -> (L.Bot, L.Bot)
                    | L.Neg0 -> (L.Neg, L.Neg))
             | L.Zero -> (L.Bot, L.Bot)
             | L.Pos0 ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (L.Pos, L.Pos)
                    | L.Pos -> (L.Pos, L.Pos)
                    | L.Neg -> (L.Bot, L.Bot)
                    | L.Zero -> (L.Bot, L.Bot)
                    | L.Pos0 -> (L.Pos, L.Pos)
                    | L.Neg0 -> (L.Bot, L.Bot))
             | L.Neg0 ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (L.Neg, L.Neg)
                    | L.Pos -> (L.Bot, L.Bot)
                    | L.Neg -> (L.Neg, L.Neg)
                    | L.Zero -> (L.Bot, L.Bot)
                    | L.Pos0 -> (L.Bot, L.Bot)
                    | L.Neg0 -> (L.Neg, L.Neg)))
      | L.Neg ->
          (match n1 with
             | L.Bot -> (L.Bot, L.Bot)
             | L.Top ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (L.Neg, L.Pos)
                    | L.Neg -> (L.Pos, L.Neg)
                    | L.Zero -> (L.Bot, L.Bot)
                    | L.Pos0 -> (L.Neg, L.Pos)
                    | L.Neg0 -> (L.Pos, L.Neg))
             | L.Pos ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (L.Pos, L.Neg)
                    | L.Pos -> (L.Bot, L.Bot)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (L.Bot, L.Bot)
                    | L.Pos0 -> (L.Bot, L.Bot)
                    | L.Neg0 -> (L.Pos, L.Neg))
             | L.Neg ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (L.Neg, L.Pos)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (L.Bot, L.Bot)
                    | L.Zero -> (L.Bot, L.Bot)
                    | L.Pos0 -> (L.Neg, L.Pos)
                    | L.Neg0 -> (L.Bot, L.Bot))
             | L.Zero -> (L.Bot, L.Bot)
             | L.Pos0 ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (L.Pos, L.Neg)
                    | L.Pos -> (L.Bot, L.Bot)
                    | L.Neg -> (L.Pos, L.Neg)
                    | L.Zero -> (L.Bot, L.Bot)
                    | L.Pos0 -> (L.Bot, L.Bot)
                    | L.Neg0 -> (L.Pos, L.Neg))
             | L.Neg0 ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (L.Neg, L.Pos)
                    | L.Pos -> (L.Neg, L.Pos)
                    | L.Neg -> (L.Bot, L.Bot)
                    | L.Zero -> (L.Bot, L.Bot)
                    | L.Pos0 -> (L.Neg, L.Pos)
                    | L.Neg0 -> (L.Bot, L.Bot)))
      | L.Zero ->
          (match n1 with
             | L.Bot -> (L.Bot, L.Bot)
             | L.Top ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (L.Zero, L.Pos)
                    | L.Neg -> (L.Zero, L.Neg)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Pos ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (L.Pos, L.Zero)
                    | L.Pos -> (L.Bot, L.Bot)
                    | L.Neg -> (L.Bot, L.Bot)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (L.Pos, L.Zero)
                    | L.Neg0 -> (L.Pos, L.Zero))
             | L.Neg ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (L.Neg, L.Zero)
                    | L.Pos -> (L.Bot, L.Bot)
                    | L.Neg -> (L.Bot, L.Bot)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (L.Neg, L.Zero)
                    | L.Neg0 -> (L.Neg, L.Zero))
             | L.Zero ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Pos0 ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (L.Zero, L.Pos)
                    | L.Neg -> (L.Zero, L.Neg)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Neg0 ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (L.Zero, L.Pos)
                    | L.Neg -> (L.Zero, L.Neg)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2)))
      | L.Pos0 ->
          (match n1 with
             | L.Bot -> (L.Bot, L.Bot)
             | L.Top ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Pos ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Neg ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Zero ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Pos0 ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Neg0 ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2)))
      | L.Neg0 ->
          (match n1 with
             | L.Bot -> (L.Bot, L.Bot)
             | L.Top ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Pos ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Neg ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Zero ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Pos0 ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2))
             | L.Neg0 ->
                 (match n2 with
                    | L.Bot -> (L.Bot, L.Bot)
                    | L.Top -> (n1, n2)
                    | L.Pos -> (n1, n2)
                    | L.Neg -> (n1, n2)
                    | L.Zero -> (n1, n2)
                    | L.Pos0 -> (n1, n2)
                    | L.Neg0 -> (n1, n2)))
  
  let const n =
    if n=0 then L.Zero
    else if n>0 then L.Pos
    else L.Neg

  let backward_comp = function
    | Syntax.Eq -> backward_eq
    | Syntax.Neq -> backward_neq
    | Syntax.Lt -> backward_lt
    | Syntax.Le -> backward_le

  let forward_binop = function
    | Syntax.Add -> forward_add
    | Syntax.Sub -> forward_sub
    | Syntax.Mult -> forward_mult

  let backward_binop = function
    | Syntax.Add -> backward_add
    | Syntax.Sub -> backward_sub
    | Syntax.Mult -> backward_mult

end
