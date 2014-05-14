(* Copyright (c) 2013, IMDEA Software Institute.              *)
(* See ../../LICENSE for authorship and licensing information *)

(** Age abstract domain: keeps track of the ages of variables 
representing lines of memory

 - the ages of the variables range between 0 and [max_age], where [max_age] 
   is the default value
 - it knows that the variables names are partitioned into sets
 - it knows what a valid cache configuration is 
(e.g. variables from one set cannot have the same age, unless it is [max_age])
 - it can count the number of valid cache configurations *)

open Big_int
open AD.DS
open NumAD.DS

(** The signature of the Age abstract domain *)
module type S = sig
  include AD.S
  
  (** {6 Initialization} *)
  
  val init : int -> (var -> int) -> (var->string) -> t
  (** [init max_val pfn v2s] initializes the abstract domain
       with a maximal value [max_val]. 
       [pfn] is a partitioning function of the variables according to their 
       name and is used for counting. 
       [v2s] is a function which converts variable names to strings. *)
  
  (** {6 Variable manipulation} *)

  val inc_var : t -> var -> t
  (** Increment variable, does not increase above the [max_val] *)
  val set_var : t -> var -> int -> t
  (** Set variable to a value;
     if variable does not exist, create it *)
  val delete_var : t -> var -> t
  (** Delete a variable *)
  val permute : t -> (int -> int) -> var -> t
  (** [permute perm x] applies a permutation [perm] to the values of variable [x].
      This is used by the [PLRU] cache replacement strategy. *)
  
  (** {6 Value acquisition} *)
  
  val get_values : t -> var -> int list
  (** Get a list with the possible values of a variable *)
  val exact_val : t -> var -> int -> (t add_bottom)
  (** [exact_val x a] returns the environments where variable [x] takes exactly
      value [a] *)
  val comp : t -> var -> var -> (t add_bottom)*(t add_bottom)
  (** [comp env x1 x2] filters the domain according to a comparison between 
     variables [x1] and [x2].
     The first result overapproximates the cases when [x1] < [x2] and
     the second one when [x1] > [x2]. *)
  val comp_with_val : t -> var -> int -> (t add_bottom)*(t add_bottom)
  (** [comp env x a] filters the domain according to whether variable [x] 
     takes values smaller than [a] or not.
     The first result contains the values where [x] < [a], and the second one 
     the values where [x] >= [a]. *)
  
  (** {6 Counting} *)

  val count_cstates: t -> big_int * big_int
  (** Count the possible valid cache states; returns a tuple 
      [(num_shared,num_disjoint)] representing the number of cache states
       for an adversary with shared memory and for an adversary with  
       disjoint memory*)
end

(** Functor creating the age abstract domain given a value abstract domain *)
module Make :
  functor (V : NumAD.S) -> S

