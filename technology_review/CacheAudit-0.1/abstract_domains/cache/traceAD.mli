(* Copyright (c) 2013, IMDEA Software Institute.              *)
(* See ../../LICENSE for authorship and licensing information *)


(** Trace abstract domain: keeps track of the possible traces, i.e., successions of cache
    {i hits} and {i misses}
 *)

(** Internally, an the possible traces are stored in a prefix graph data 
    structure, where nodes store the effect of assembly instructions to the cache, 
    which can be a {i cache hit}, a {i cache miss}, or {i no cache access}. *)

(** A functor which results in a cache abstract domain, enriched with the 
    capabilities of keeping track of traces, i.e., it incorporates a 
    trace abstract domain *)
module Make :
  functor (C : CacheAD.S) -> CacheAD.S
