(* © Copyright University of Birmingham, UK *)

open Common
open Phi
open Product
open Triple

type t = {
  (* NFA being analysed *)
  nfa : Nfa.t;
  (* pumpable kleene being analysed *)
  ik : int;
  (* set of branch points that makes the kleene pumpable *)
  brset : IntSet.t;
  (* current prefix *)
  w : Word.t;
  (* set of products seen so far *)
  mutable pcache : ProductSet.t;
  (* set of triples seen so far *)
  mutable tcache : TripleSet.t;
  (* machine component - triples reached *)
  mutable tpls : (Word.t * Triple.t) list;
  (* machine component - products to be evolved *)
  mutable evolve : (Word.t * Product.t) list;
  (* machine component - products to be advanced *)
  mutable advance : (Word.t * Product.t) list;
  (* processing flags *)
  mutable flgs : Flags.t;
};;

let init (nfa, w, p) (ik, brset) = {
  nfa = nfa;
  ik = ik;
  brset = brset;
  w = w;
  pcache = ProductSet.empty;
  tcache = TripleSet.empty;
  tpls = [];
  (* start with evolving the kleene state and the corresponding phi *)
  evolve = [(w, Product.make ik p)];
  advance = [];
  flgs = Flags.empty
};;

let next m =
  let rec explore () = match (m.tpls, m.evolve, m.advance) with
    |((w, tpl) :: t, _, _) ->
      m.tpls <- t;
      if not (TripleSet.mem tpl m.tcache) then (
        (* never seen before triple, return *)
        m.tcache <- TripleSet.add tpl m.tcache;
        Some (Word.suffix w (Word.length m.w), tpl)
      ) else explore ()
    |([], (w, p) :: t, _) ->
      m.evolve <- t;
      (* evolve product looking for triples *)
      let (flgs, ep, tpls) = Product.evolve (m.nfa, w, p) m.brset in
      m.flgs <- Flags.union flgs m.flgs;
      m.tpls <- List.map (fun tpl -> (w, tpl)) tpls;
      (* resulting product needs to be further advanced *)
      m.advance <- (w, ep) :: m.advance;
      explore ()
    |([], [], (w, p) :: t) ->
      m.advance <- t;
      if not (ProductSet.mem p m.pcache) then (
        (* never seen before product, advance *)
        m.pcache <- ProductSet.add p m.pcache;
        m.evolve <- Product.advance (m.nfa, w, p);
        explore ()
      ) else explore ()
    |([], [], []) ->
      None in
  explore ();;

let flags m = m.flgs;;
