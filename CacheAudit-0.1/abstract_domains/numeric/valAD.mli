(* Copyright (c) 2013, IMDEA Software Institute.              *)
(* See ../../LICENSE for authorship and licensing information *)

(** Value abstract domain: overapproximates possible values of
    variables by sets and intervals *)


(** Module type for describing options of the value abstract domain *)
module type VALADOPT = sig 
  (** Threshold for returning dedicated environment with each
      variable value *)
  val max_get_var_size : int 

  (** Threshold for switching from explicit set representation to
      intervals (and back) *)
  val max_set_size : int 
end

(** Options for saving memory during analysis *)
module ValADOptForMemory : sig 
  val max_get_var_size : int 
  val max_set_size : int 
end

(** Creates a numeric abstract domain with the given options *)
module Make : functor (O : VALADOPT) -> NumAD.S
