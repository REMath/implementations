(* © Copyright University of Birmingham, UK *)

open Common
open Phi

type t = {
  (* NFA being analysed *)
  nfa : Nfa.t;
  (* current prefix *)
  w : Word.t;
  (* set of phis seen so far *)
  mutable cache : PhiSet.t;
  (* machine component - phis to be checked for non-acceptance *)
  mutable evolve : (Word.t * Phi.t) list;
  (* machine component - phis to be advanced *)
  mutable advance : (Word.t * Phi.t) list;
  (* processing flags *)
  mutable flgs : Flags.t;
};;

let init (nfa, w, p) = {
  nfa = nfa;
  w = w;
  cache = PhiSet.empty;
  (* start with evolving the given phi *)
  evolve = [(w, p)];
  advance = [];
  flgs = Flags.empty
};;

let next m =
  let rec explore () = match (m.evolve, m.advance) with
    |((w, p) :: t, _) ->
      m.evolve <- t;
      begin
        (* evolve phi *)
        let (flgs, ep) = Phi.evolve (m.nfa, w, p) None in
        if Flags.is_accepting flgs then
          (* we cannot advance this phi - prefix matching takes over *)
          explore ()
        else if Flags.is_eoihit flgs then (
          (* we may be able to get rid of the EOI/END with a character *)
          m.advance <- (w, ep) :: m.advance;
          explore ()
        ) else (
          (* non-accepting state reached, return *)
          Some (Word.suffix w (Word.length m.w), ep)
        )
      end
    |([], (w, ep) :: t) ->
      m.advance <- t;
      if not (PhiSet.mem ep m.cache) then (
        (* never seen before phi, need to be explored *)
        m.cache <- PhiSet.add ep m.cache;
        let (advanced, nomatch) = Phi.explore (m.nfa, w, ep) in
        (* schedule the resulting phis to be checked for non-acceptance *)
        m.evolve <- advanced;
        begin
          (* check if there are no-match characters *)
          match nomatch with
            |[] -> explore ()
            |(u, v) :: _ -> Some (Word.suffix (Word.extend w (u, v)) (Word.length m.w), Phi.make IntSet.empty)
        end
      ) else explore ()
    |([], []) ->
      None in
  explore ();;

let flags m = m.flgs;;
