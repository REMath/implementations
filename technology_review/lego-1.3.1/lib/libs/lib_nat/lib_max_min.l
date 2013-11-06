Module lib_max_min Import lib_nat_Prop_rels;

(* Contents
   --------
   o Functions which compute the maximum and the minimum of a pair of
     natural numbers.
   o Theorems about these functions.

   Changes
   -------

   $Log: lib_max_min.l,v $
   Revision 1.2  1997/11/02 14:50:58  tms
   Replaced Immed by Try Immed


   29 Jan 97 Thomas Schreiber <tms@dcs.ed.ac.uk>
   added max_assoc, max_suc_pred
*)

max == nat_diagonal_iter ([n:nat]n) ([n:nat]n) suc;
min == nat_diagonal_iter ([n:nat]zero) ([n:nat]zero) suc;

Goal max_Le_left : {x,y:nat}Le x (max x y);
intros;
Refine nat_diagonal_ind  [x,y:nat]Le x (max x y);
intros;
Refine Le_zero_n;
intros;
Refine eq_imp_Le;
Refine Eq_refl;
intros; 
Refine Le_resp_suc;
Refine H;
Save max_Le_left;

Goal max_Le_right : {x,y:nat}Le y (max x y);
intros;
Refine nat_diagonal_ind  [x,y:nat]Le y (max x y);
intros;
Refine eq_imp_Le;
Refine Eq_refl;
intros;
Refine Le_zero_n;
intros; 
Refine H;
intros;
Refine Le_resp_suc; Refine H;
Save max_Le_right;

Goal max_is_least : {x,y,z:nat}(Le x z) -> (Le y z) -> (Le (max x y) z);
intros x y;
Refine nat_diagonal_ind [x,y:nat]({z:nat}(Le x z)->(Le y z)->Le (max x y) z);
intros;
Refine H1;
intros;
Refine H;
Intros n m H z;
Refine nat_ind [z:nat]((Le (suc n) z)->(Le (suc m) z)->Le (max (suc n) (suc m)) z);
intros;
Refine not_Le_zero_n;
Next +1; Refine H2;
intros;
Equiv Le (suc (max n m)) ?;
Refine Le_resp_suc;
Refine H;
Refine Le_resp_pred;
Refine H2;
Refine Le_resp_pred;
Refine H3;
Save max_is_least;

Goal min_Le_left : {x,y:nat}Le (min x y)  y;
intros;
Refine nat_diagonal_ind  [x,y:nat]Le (min x y) y;
intros;
Refine Le_zero_n;
intros;
Refine Le_zero_n;
intros; 
Refine Le_resp_suc; Refine H;
Save min_Le_left;

Goal min_Le_right : {x,y:nat}Le (min x y) x;
intros;
Refine nat_diagonal_ind  [x,y:nat]Le (min x y) x;
intros;
Refine Le_zero_n;
intros;
Refine Le_zero_n;
intros; 
Refine Le_resp_suc; Refine H;
Save min_Le_right;

Goal min_is_greatest : {x,y,z:nat}(Le z x) -> (Le z y) -> (Le z (min x y));
intros x y;
Refine nat_diagonal_ind [x,y:nat]{z:nat}(Le z x)->(Le z y)->Le z (min x y);
intros;
Refine H;
intros;
Refine H1;
Intros n m H z;
Refine nat_ind [z:nat](Le z (suc n))->(Le z (suc m))->Le z (min (suc n) (suc m));
intros;
Refine Le_zero_n;
intros;
Equiv Le ? (suc (min n m));
Refine Le_resp_suc;
Refine H;
Refine Le_resp_pred;
Refine H2;
Refine Le_resp_pred;
Refine H3;
Save min_is_greatest;

Goal max_sym : {n,m:nat}(Eq (max n m) (max m n));
intros;
Refine nat_diagonal_ind [n,m:nat]Eq (max n m) (max m n);
Intros m;
Refine nat_ind [m1:nat]Eq (max zero m1) (max m1 zero);
Refine Eq_refl;
intros;
Refine Eq_refl;  (* Trivial use of induction as case analysis *)
intros;
Refine Eq_refl;   (* Don't need it here because of change to nat_diagonal_ind*)
intros;
Refine Eq_resp suc;
Refine H;
Save max_sym;

Goal max_assoc : {m,n,o:nat}Eq (max (max m n) o) (max m (max n o));
Induction m;

  intros; Refine Eq_refl;	(* m=0 *)

  (** step case **)
  intros m ih;
  Induction n;
    intros; Refine Eq_refl;	(* m>0 & n=0 *)

    (** m>0 & n>0 **)
    intros n ih'; Induction o;
    Refine Eq_resp suc; Refine Eq_refl; (* m>0 & n>0 & o=0 *)

      (** m>0 & n>0 & o>0 **)
      intros; Refine Eq_resp suc; Try Immed;
Save max_assoc;

Goal max_suc_pred : {m,n:nat}Eq (max m (suc n)) (suc (max (pred m) n));
Induction m;
    intros; Refine Eq_refl;	(* base case *)

    (** step case **)
    intros m ih _; Refine Eq_refl;
Save max_suc_pred;

Goal min_sym : {n,m:nat}(Eq (min n m) (min m n));
intros;
Refine nat_diagonal_ind [n,m:nat]Eq (min n m) (min m n);
Intros m;
Refine nat_ind [m1:nat]Eq (min zero m1) (min m1 zero);
Refine Eq_refl;
intros;
Refine Eq_refl;  (* Trivial use of induction as case analysis *)
intros;
Refine Eq_refl;   (* Don't need it here because of change to nat_diagonal_ind*)
intros;
Refine Eq_resp suc;
Refine H;
Save min_sym;


Goal Le_min_left : {x,y:nat}(Le x y) -> (Eq (min x y) x);
intros;
Refine Le_antisym;
Refine min_is_greatest;
Refine eq_imp_Le;
Refine Eq_refl;
Refine H;
Refine min_Le_right;
Save Le_min_left;

Goal Le_min_right : {x,y:nat}(Le y x) -> (Eq (min x y) y);
intros;
Refine Le_antisym;
Refine min_is_greatest;
Refine H;
Refine eq_imp_Le;
Refine Eq_refl;
Refine min_Le_left;
Save Le_min_right;

Goal Le_max_right : {x,y:nat}(Le x y) -> (Eq (max x y) y);
intros;
Refine Le_antisym;
Refine max_Le_right;
Refine max_is_least;
Refine H;
Refine eq_imp_Le;
Refine Eq_refl;
Save Le_max_right;

Goal Le_max_left : {x,y:nat}(Le y x) -> (Eq (max x y) x);
intros;
Refine Le_antisym;
Refine max_Le_left;
Refine max_is_least;
Refine eq_imp_Le;
Refine Eq_refl;
Refine H;
Save Le_max_left;

Goal min_idemp : {a:nat}Eq (min a a) a;
Refine nat_elim [a:nat]Eq (min a a) a;
Refine Eq_refl;			(* base case *)
intros n ind_hyp; Refine Eq_resp suc; Try Immed;
Save;
(* end of new axiomatisation *)

Goal max_resp_times : {x,y,a:nat}Eq (max (times a x) (times a y)) (times a (max x y));
intros;
Refine Le_antisym;
Refine decide_nat x y;
intros;
Refine Le_trans;
Refine +2 max_Le_right;
Refine Le_resp_times;
Refine max_is_least;
Refine H;
Refine eq_imp_Le;
Refine Eq_refl;
intros;
Refine Le_trans;
Refine +2 max_Le_left;
Refine Le_resp_times;
Refine max_is_least;
Refine eq_imp_Le;
Refine Eq_refl;
Refine Lt_imp_Le;
Refine H;
Refine max_is_least;
Refine Le_resp_times;
Refine max_Le_left;
Refine Le_resp_times;
Refine max_Le_right;
Save max_resp_times;

Goal min_resp_times : {x,y,a:nat}Eq (min (times a x) (times a y)) (times a (min x y));
intros;
Refine Le_antisym;
Refine min_is_greatest;
Refine Le_resp_times;
Refine min_Le_right;
Refine Le_resp_times;
Refine min_Le_left;
Refine decide_nat x y;
intros;
Refine Le_trans;
Refine +1 min_Le_right;
Refine Le_resp_times;
Refine min_is_greatest;
Refine eq_imp_Le;
Refine Eq_refl;
Refine H;
intros;
Refine Le_trans;
Refine +1 min_Le_left;
Refine Le_resp_times;
Refine min_is_greatest;
Refine Lt_imp_Le;
Refine H;
Refine eq_imp_Le;
Refine Eq_refl;
Save min_resp_times;


Goal max_resp_plus : {a,b,x:nat}(Eq (max (plus a x) (plus b x)) (plus (max a b) x));
intros;
Qrepl plus_commutes a x;
Qrepl plus_commutes b x;
Qrepl plus_commutes (max a b) x;
Refine nat_ind [x:nat](
Eq (max (plus x a) (plus x b)) (plus x (max a b)));
Refine Eq_refl;
intros;
Refine Eq_resp suc;
Refine H;
Save max_resp_plus;

Goal min_resp_plus : {a,b,x:nat}(Eq (min (plus a x) (plus b x)) (plus (min a b) x));
intros;
Qrepl plus_commutes a x;
Qrepl plus_commutes b x;
Qrepl plus_commutes (min a b) x;
Refine nat_ind [x:nat](
Eq (min (plus x a) (plus x b)) (plus x (min a b)));
Refine Eq_refl;
intros;
Refine Eq_resp suc;
Refine H;
Save min_resp_plus;













