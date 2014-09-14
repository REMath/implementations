(* © Copyright University of Birmingham, UK *)

open Common
open Triple

type t = {
  (* NFA being analysed *)
  nfa : Nfa.t;
  (* pumpable kleene being analysed *)
  ik : int;
  (* current prefix *)
  w : Word.t;
  (* set of triples seen so far *)
  mutable cache : TripleSet.t;
  (* machine component - triples to be checked for convergence *)
  mutable evolve : (Word.t * Triple.t) list;
  (* machine component - triples to be advanced *)
  mutable advance : (Word.t * Triple.t) list;
  (* processing flags *)
  mutable flgs : Flags.t;
};;

let init (nfa, w, tpl) ik = {
  nfa = nfa;
  ik = ik;
  w = w;
  cache = TripleSet.empty;
  evolve = [];
  (*
    - start with advancing the given triple
    - y2 can't be empty since it also includes the first branching character ('a' in y1ay2)
  *)
  advance = [(w, tpl)]; 
  flgs = Flags.empty;
};;

let next m =
  let rec explore () = match (m.evolve, m.advance) with
    |((w, tpl) :: t, _) ->
      m.evolve <- t;
      let (i, j, p) = elems tpl in
      (* evolve the phi component *)
      let (flgs, ep) = Phi.evolve (m.nfa, w, p) None in
      let etpl = Triple.make i j ep in
      m.flgs <- Flags.union flgs m.flgs;
      if not (TripleSet.mem etpl m.cache) then (
        (* never seen before triple, check for convergence *)
        m.cache <- TripleSet.add etpl m.cache;
        if (Util.is_epsilon_reachable m.nfa w i m.ik) && (Util.is_epsilon_reachable m.nfa w j m.ik) then
          (* converges, return *)
          Some (Word.suffix w (Word.length m.w), ep)
        else (
          (* needs to be advanced further *)
          m.advance <- (w, etpl) :: m.advance;
          explore ()
        )
      ) else explore ()
    |([], (w, tpl) :: t) ->
      m.evolve <- Triple.advance (m.nfa, w, tpl);
      m.advance <- t;
      explore ()
    |([], []) ->
      None in
  explore ();;

let flags m = m.flgs;;
