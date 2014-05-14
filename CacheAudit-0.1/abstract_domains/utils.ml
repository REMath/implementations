(* Copyright (c) 2013, IMDEA Software Institute.             *)
(* See ../LICENSE for authorship and licensing information   *)

open Big_int
open NumAD.DS

let log2 x = log10 (float_of_big_int x) /. (log10 2.)

let prod l = List.fold_left (fun accum x -> 
  mult_big_int (big_int_of_int64 x) accum) unit_big_int l

let partition elts pfn = 
  NumSet.fold (fun addr csets -> 
  let bnr = (pfn addr) in
  let naset = try 
      IntMap.find bnr csets 
    with Not_found -> NumSet.empty in
  let naset = NumSet.add addr naset in
  IntMap.add bnr naset csets) elts IntMap.empty
