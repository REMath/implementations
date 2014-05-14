Module lib_nat Import lib_bool;
(*
Invoke

sed -f ~lego/library/util/changeLib.sed < lib_nat.l > ~lego/library/new/lib_Type/lib_nat.l

*)

(* Contents
   --------
   o Definition and induction principles for the datatype "nat" of natural
     numbers.
   o Constructor identifiers: "is_zero" and "is_suc".
   o Characterizing theorems: "zero_not_suc"; "zero_or_suc".
   o Various basic function about natural numbers.


   Changes
   -------

   Conor McBride <ctm@dcs.ed.ac.uk>
   2 Jun 1998
   adding suc_n_not_n theorem so Qnify lemmes de finitude work

   Thomas Schreiber <lego@dcs.ed.ac.uk>
   21 Feb 1995
   getting this module to work with the theory XCC' 

   Thomas Schreiber <lego@dcs.ed.ac.uk>
   16 Jan 1995
   o getting this module to work in an impredicative setting
*)

Inductive [nat:Type] ElimOver Type Theorems
Constructors [zero:nat][suc:nat->nat];

[    nat_rec = [t|Type]nat_elim ([_:nat]t)
             : {t|Type}t->(nat->t->t)->nat->t
]
[    nat_iter = [t|Type][x:t][f:t->t]nat_rec x ([_:nat]f)
             : {t|Type}t->(t->t)->nat->t 
]
[    nat_ind = [P:nat->Prop]nat_elim P
             : {P:nat->Prop}(P zero)->({n:nat}(P n)->P (suc n))->{n:nat}P n 
];


Goal nat_double_elim : {T:nat->nat->Type}
     (T zero zero)->
     ({n:nat}(T zero n)->(T zero (suc n)))->
     ({m:nat}({n:nat}T m n)->T (suc m) zero)->
     ({m:nat}({n:nat}T m n)->{n:nat}(T (suc m) n)->T (suc m) (suc n))->
     {m,n:nat}T m n;
intros T bb_step bs_step sb_step ss_step;
Refine nat_elim [m:nat]{n:nat}T m n; Refine nat_elim (T zero); Immed;
intros m h; Refine nat_elim (T (suc m));
Refine sb_step m h; Refine ss_step m h;
SaveUnfrozen nat_double_elim;


Goal nat_diagonal_iter : {C|Type}(nat -> C) -> (nat -> C) -> (C -> C)
  -> (nat -> nat -> C);
Intros C fst_zero snd_zero inc;
Refine (nat_rec|(nat -> C) ? ?);
Refine fst_zero;
Intros n f;
Refine nat_rec;
Refine snd_zero (suc n);
intros H _;
Refine inc (f H);
SaveUnfrozen nat_diagonal_iter;

Goal nat_diagonal_ind : {phi:nat->nat->Prop}({m:nat}(phi zero m)) ->
   ({n:nat}(phi (suc n) zero)) -> 
    ({n,m:nat}((phi n m) ->(phi (suc n) (suc m))))
  -> {n,m:nat}(phi n m);
intros;
Refine nat_ind [n:nat]{m:nat}(phi n m);
Refine H;
intros;
Refine nat_ind [m:nat](phi (suc ?) m);
Refine H1;
intros;
Refine H2;
Immed;
Save nat_diagonal_ind;

nat_d_rec_for_int == [C:nat->nat->Type][d:C zero zero]
[e:{m,n:nat}(C m n)->C (suc m) n][f:{m,n:nat}(C m n)->C m (suc n)][m,n:nat]
nat_elim ([x:nat]C x n) (nat_elim ([x:nat]C zero x) d (f zero) n) ([x:nat]e x n) m;

(* Special double induction to define induction on integers... *)



[    is_suc = [n:nat] Ex[m:nat] Eq (suc m) n
             : nat->Prop 
]
[    is_zero = [n:nat] Eq zero n
             : nat->Prop 
];


Goal zero_not_suc : {n:nat}not (Eq zero (suc n));
Intros n H;
Refine true_not_false;
Refine Eq_resp (nat_rec true ([_:nat][_:bool]false)) H;
Save zero_not_suc;

Goal suc_not_zero : not (is_suc zero);
Intros h;
Refine h;
intros;
Refine zero_not_suc t;
Refine Eq_sym H;
Save suc_not_zero; 

(*** this does not work in an impredicative setting
Goal zero_not_suc : {n:nat}not (Eq zero (suc n));
Intros n h;
[IsZero = nat_iter trueProp ([_:Prop]absurd)];
Equiv IsZero (suc n); Qrepl (Eq_sym h); Refine PropId;
Save zero_not_suc;                                                        


Goal suc_not_zero : not (is_suc zero);
Intros h;
[IsSuc = nat_iter absurd ([_:Prop]trueProp)];
Equiv IsSuc zero; 
exE h; intros t h1; Qrepl (Eq_sym h1); Refine PropId;
Save suc_not_zero; 
***)

(**** This proof uses Qnify and extends it with acyclicity proofs ****)
Goal suc_n_not_n : {n:nat}not (Eq (suc n) n);
Induction n Then Expand not Then Qnify;
Refine x1_ih; Immed;
Save;
Configure Qnify nat suc_n_not_n;

Goal zero_or_suc : {n:nat}or (Eq n zero) (is_suc n);
Refine nat_ind ([n:nat]or (Eq n zero) (is_suc n));
Refine inl; Refine Eq_refl;
intros; Refine inr; exI ?; Refine +1 Eq_refl;
Save zero_or_suc;                                                       


[    one = suc zero : nat]
[    two = suc one : nat]
[    three = suc two : nat]
[    four = suc three : nat]
[    five = suc four : nat]
[    six = suc five : nat]
[    seven = suc six : nat]
[    eight = suc seven : nat]
[    nine = suc eight : nat]
[    ten = suc nine : nat
]
[    plus = [m,n:nat] nat_iter n suc m
           : nat->nat->nat
]
[    times = [m,n:nat] nat_iter zero (plus n) m
           : nat->nat->nat 
]
[    exp = [m,n:nat] nat_iter one (times m) n
           : nat->nat->nat 
]
[    pred = nat_rec zero [n,_:nat]n (* truncated pred *)
           : nat->nat 
]
[    minus = [m,n:nat] nat_iter m pred n 
           : nat->nat->nat 
]
[    ackerman = nat_rec (plus one)
                        [_:nat][f:nat->nat]
                            nat_rec (f one)
                                   ([_,n:nat] f n) 
           : nat->nat->nat 
]
[    if_zero = [t|Type][n:nat][x,y:t] nat_iter x ([_:t]y) n
           : {t|Type}nat->t->t->t 
];

Goal fact : nat -> nat;
  Refine nat_elim [n:nat]nat;
    Refine one;			(* 0! = 1 *)
    intros n fact_n;
    Refine times (suc n) fact_n;	(* (n+1)! = (n+1) * n! *)
Save fact;

Goal zero_not_one : not (Eq zero one);
Refine zero_not_suc;
Save zero_not_one;













