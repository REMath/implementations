Module lib_prod Import lib_eq_basics;

(* Contents
   --------
   o The product datatype.
*)
 
Inductive [prod:SET] ElimOver TYPE Theorems
Parameters [A,B?SET]
Constructors [Pair:{a:A}{b:B}prod];

Discharge A;

pair1 [A,B:SET][a:A][b:B] == Pair a b;

[s,t?SET];

(*

$[prod : SET->SET->SET];

$[Pair:s->t->(prod s t)];

$[prod_elim : {T:(prod s t)->TYPE}
               ({a:s}{b:t}T (Pair a b))->
                 {p:prod s t}T p];

[[T:(prod s t)->TYPE][e:{a:s}{b:t}T (Pair a b)][a:s][b:t]
  prod_elim T e (Pair a b) ==> e a b];
*)
[    prod_rec = [u|TYPE]prod_elim [_:prod s t]u
            : {u|TYPE}(s->t->u)->(prod s t)->u
]
[    prod_ind = [P:(prod s t)->Prop]prod_elim P
            : {P:(prod s t)->Prop}
              ({a:s}{b:t}P (Pair a b))->
                {p:prod s t}P p
]
[    Fst = prod_rec [a:s][_:t]a

            : (prod s t)->s
]
[    Snd = prod_rec [_:s][b:t]b
            : (prod s t)->t
];

Goal prod_eta : {p:prod s t}Eq p (Pair (Fst p) (Snd p));
Refine prod_ind[p:prod s t]Eq p (Pair (Fst p) (Snd p));
intros;
Refine Eq_refl;
Save prod_eta;

Goal prod_ext : {p,q:prod s t}(Eq (Fst p) (Fst q))->(Eq (Snd p) (Snd q))->Eq p q;
intros;
Qrepl prod_eta p;
Qrepl H;
Qrepl H1;
Refine Eq_sym (prod_eta ?);
Save prod_ext;

Discharge s;

