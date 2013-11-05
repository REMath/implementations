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
  functor (AbEnv:Abstraction.Env) ->
struct
  
  module M = Map.Make(struct type t = label let compare = compare end)
    
  let get default m k =
    try
      M.find k m 
    with
	Not_found -> default

  let get_equation = get []

  let make_eq_sys (constraints : (label * (AbEnv.L.t -> AbEnv.L.t) * label) list) =
    List.fold_left
      (fun sys (l1,f,l2) -> M.add l2 ((l1,f)::(get_equation sys l2)) sys)
      M.empty
      constraints

  let get_abenv s l = get (AbEnv.L.bottom ()) s l
  let rec apply_eq s = function
    | [] -> AbEnv.L.bottom ()
    | [l,f] -> f (get_abenv s l)
    | (l,f)::q -> AbEnv.L.join (f (get_abenv s l)) (apply_eq s q)

  let modify s k f =
    M.add k (f (get_abenv s k)) s

  type strategy =
    | Empty
    | Single of label
    | Seq of strategy * strategy
    | Loop of label * strategy 

  let rec gen_strategy = function 
    | Syntax.Skip l -> Single l
    | Syntax.Assign (l,x,e) -> Single l
    | Syntax.If (l,t,b1,b2) -> Seq (Single l, Seq (gen_strategy b1, gen_strategy b2))
    | Syntax.While (l,t,b) -> Loop (l, gen_strategy b)
    | Syntax.Seq (i1,i2) -> Seq (gen_strategy i1, gen_strategy i2)

  let strategy (p,l) = 
    Seq (gen_strategy p,Single l)

  let rec iter l0 sys strat s =
    match strat with
      | Empty ->  s
      | Single l -> 
	  let new_val = 
	    if l=l0 
	    then AbEnv.L.join (AbEnv.init_env ()) (apply_eq s (get_equation sys l))
	    else apply_eq s (get_equation sys l)
	  in M.add l new_val s
      | Seq (strat1,strat2) ->
	   iter l0 sys strat2 (iter l0 sys strat1 s)
      | Loop (l,strat) ->
	  let s = iter  l0 sys (Single l) s in
	    let rec loop_widen s =
	      let s' = iter l0 sys (Seq (strat,Single l)) s in
		if AbEnv.L.order_dec (get_abenv s' l) (get_abenv s l) then iter l0 sys strat s
		else loop_widen (modify s' l (AbEnv.L.widen (get_abenv s l)))
	    in
	    let rec loop_narrow s =
	      let s' = iter l0 sys (Seq (strat,Single l)) s in
		if AbEnv.L.order_dec  (get_abenv s l) (get_abenv s' l) then iter l0 sys strat s
		else loop_narrow (modify s' l (AbEnv.L.narrow (get_abenv s l)))
	    in
	      loop_narrow (loop_widen s)

  let gen_constraints p =
    List.map
      (function (l1,i,l2) ->
	 match i with
	   | Cfg.Assign (x,e) -> (l1,AbEnv.assign x e,l2)
	   | Cfg.Assert t -> (l1,AbEnv.backward_test t,l2)
      )
      (Cfg.build p)

  let check p res =
    List.iter
      (function (l1,i,l2) ->
	 if
	   (match i with
	      | Cfg.Assign (x,e) -> AbEnv.L.order_dec (AbEnv.assign x e (res l1)) (res l2)
	      | Cfg.Assert t -> AbEnv.L.order_dec (AbEnv.backward_test t (res l1)) (res l2))
	 then ()
	 else failwith (Printf.sprintf "wrong postfixpoint in edges (%d -> %d)\n" l1 l2))
      (Cfg.build p)

  let solve p =
    AbEnv.init (Syntax.vars p);
    let f = get_abenv
	      (iter (Cfg.entry (fst p)) (make_eq_sys (gen_constraints p)) (strategy p) M.empty) in
      check p f; f

  let solve_and_print p =
	let f = solve p in
      function l -> AbEnv.L.to_string (f l)


end
