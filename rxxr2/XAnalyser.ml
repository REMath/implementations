(* © Copyright University of Birmingham, UK *)

open Common
open Beta
open Phi

type t = {
  (* NFA being analysed *)
  nfa : Nfa.t;
  (* set of pumpable kleene states *)
  kset : IntSet.t;
  (* current prefix word *)
  mutable w : Word.t;
  (* set of betas seen so far *)
  mutable bcache : BetaSet.t;
  (* set of phis seen so far *)
  mutable pcache : PhiSet.t;
  (* machine component - current kleene hits *)
  mutable hits : (int * Beta.t) list;
  (* machine component - betas to be evolved *)
  mutable evolve : (Word.t * Beta.t) list;
  (* machine component - betas to be advanced *)
  mutable advance : (Word.t * Beta.t) list;
  (* processing flags *)
  mutable flgs : Flags.t;
};;

let init nfa kset = {
  nfa = nfa;
  kset = kset;
  w = Word.empty;
  bcache = BetaSet.empty;
  pcache = PhiSet.empty;
  (* start evolving the root state *)
  hits = []; evolve = [(Word.empty, Beta.make (Nfa.root nfa))];
  advance = [];
  flgs = Flags.empty
};;

let next m =
  let rec explore () = match (m.hits, m.evolve, m.advance) with
    (* process hits *)
    |((ik, b) :: t, _, _) ->
      m.hits <- t;
      let p = Phi.make (Beta.elems b) in
      if not (PhiSet.mem p m.pcache) then (
        (* never seen before phi, return *)
        m.pcache <- PhiSet.add p m.pcache;
        Some (ik, m.w, p)
      ) else explore ()
    |([], (w, b) :: t, _) ->
      m.evolve <- t;
      m.w <- w;
      (* look for hits *)
      let (flgs, eb, hits) = Beta.evolve (m.nfa, w, b) m.kset in
      m.hits <- hits;
      (* new beta to be advanced *)
      m.advance <- (w, eb) :: m.advance;
      m.flgs <- Flags.union flgs m.flgs;
      explore ()
    |([], [], (w, b) :: t) ->
      m.advance <- t;
      if not (BetaSet.mem b m.bcache) then (
        (* never seen before beta, advance *)
        m.bcache <- BetaSet.add b m.bcache;
        m.evolve <- Beta.advance (m.nfa, w, b);
      ); explore ()
    |([], [], []) ->
      None in
  explore();;

let flags m = m.flgs;;
