(*  Copyright (c) 2008, University of Virginia
    All rights reserved.
   
    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions
    are met:
       * Redistributions of source code must retain the above copyright
         notice, this list of conditions and the following disclaimer.
       * Redistributions in binary form must reproduce the above
         copyright notice, this list of conditions and the following
         disclaimer in the documentation and/or other materials
         provided with the distribution.
       * Neither the name of the University of Virginia  nor the names 
         of its contributors may be used to endorse or promote products
         derived from this software without specific prior written
         permission.
   
    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
    "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
    LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
    FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
    COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
    INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
    (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
    SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
    HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
    STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
    ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
    OF THE POSSIBILITY OF SUCH DAMAGE.
   
    Author: Pieter Hooimeijer
*)

(* Hashtables as sets 

   As is customary for OCaml apps, we now reimplement part of
   the standard library.
*)

type 'e hashset = Enum of ('e, bool) Hashtbl.t
		| AllElements 

let set_in (s : 'e hashset) (e : 'e) : bool = 
  match s with
    | Enum s      -> (try Hashtbl.find s e with Not_found -> false)
    | AllElements -> true

let set_size   (s : 'e hashset) : int = 
  match s with 
    | Enum s      -> Hashtbl.length s
    | AllElements -> -1

let set_empty (s : 'e hashset) : bool =
  set_size s == 0

let set_add    (s : 'e hashset) (e : 'e) : unit = 
  match s with
    | Enum s      -> Hashtbl.replace s e true
    | AllElements -> ()

(* let set_remove (s : 'e hashset) (e : 'e) : unit = Hashtbl.remove s e *)

let set_cup  (t : 'e hashset) (s : 'e hashset) : 'e hashset = 
  match t, s with 
    | Enum t, Enum s -> 
	Hashtbl.iter (fun x _ -> Hashtbl.replace t x true) s;
	Enum t
    | _, _ -> AllElements

let set_cap  (a : 'e hashset) (b : 'e hashset) : 'e hashset = 
  let itr t s e _ = (if set_in s e then
	               Hashtbl.replace t e true
		     else ()) in
    match a,b with
      | Enum a', Enum b' -> (let t = Hashtbl.create (max (set_size a) (set_size b)) in
			     if (set_size a > set_size b) then
			       Hashtbl.iter (itr t a) b'
			     else
			       Hashtbl.iter (itr t b) a';
			     Enum t)
      | Enum a', _ -> Enum a'
      | _, Enum b' -> Enum b'
      | _ -> AllElements
