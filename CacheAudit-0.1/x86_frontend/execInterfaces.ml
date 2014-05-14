(* Copyright (c) 2013, IMDEA Software Institute.             *)
(* See ../LICENSE for authorship and licensing information   *)

(* What a module reading an executable object should return *)

type section = 
  { start_addr : int64;
    end_addr   : int64; (*exclusivem that is this address is not part of the section *)
    offset     : int;
    max_valid_offset : int; (* In case all the adresses cannot be mapped into the file *)
  }
   
  
  
