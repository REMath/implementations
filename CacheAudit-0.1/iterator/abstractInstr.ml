(* Copyright (c) 2013, IMDEA Software Institute.             *)
(* See ../LICENSE for authorship and licensing information   *)


(** Module defining types for the abstract instructions used by the 
[Iterator] to communicate with the abstract domains *)

type 'a flagop = ADcmp of 'a*'a
            | ADtest of 'a*'a 
            | ADfset of X86Types.flag*bool

type memop = ADarith of X86Types.arith_op | ADmov | ADexchg

type stackop = ADpop | ADpush

type varop = Op of X86Types.arith_op | Move

