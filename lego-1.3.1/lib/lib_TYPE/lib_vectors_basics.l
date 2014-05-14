(*begin 
\typeout{Author: Thomas Schreiber
Time-stamp: <07 Mar 97 tms /home/lego/library/reorg/libs/lib_vectors/lib_vectors_basics.l>}
This module defines some basic vector functions -- where basic really
just means pure vector functions which do not require any other
datatype. 

CHANGES
-------

  7 March 1997 Thomas Schreiber <tms@dcs.ed.ac.uk>
    added theorem vect_nth_append
@*)
Module lib_vectors_basics Import lib_vectors;

[m,n|nat];

Goal vsingleton : {T|Type}T->vect T one;
intros; Refine vcons; Refine -0 vnil; Try Immed;
Save;

Goal vappend : {T|Type}(vect T m)->(vect T n) -> vect T (plus m n);
intros T;
Refine nat_elim [m:nat](vect T m)->(vect T n)->vect T (plus m n);
intros; Try Immed;			(* base case *)
intros; 
Refine vcons; 
Refine vect_head; Refine +1 H;
Refine x1_ih; 
Refine vect_tail; Try Immed;
Save;

DischargeKeep m;

Goal vtack : {T|Type}T->(vect T m)->vect T (suc m);
intros T e v; 
Equiv vect T (plus one m);
Qrepl plus_commutes one m;
Refine vappend; 
Refine -0 vsingleton e; Try Immed;
Save;

Discharge m;

Goal vect_nth_append :
  {T|Type}{n|nat}{x:fin n}{s:vect T n}{m|nat}{t:vect T m}
  Eq (vect_nth (f_plus x) (vappend t s)) (vect_nth x s);

intros ____;
Refine vect_elim [m|nat][t|vect T m]
  Eq (vect_nth (f_plus x) (vappend t s)) (vect_nth x s);

  Refine Eq_refl;		(* base case *)

  (** step case **)
  intros;
  Qrepl Eq_sym v_ih; Refine Eq_refl;
Save vect_nth_append;

(*@
end*)
