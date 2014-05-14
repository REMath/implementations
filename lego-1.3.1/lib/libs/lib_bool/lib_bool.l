Module lib_bool Import lib_eq_basics;

(* Contents
   --------
   o Definition and induction principles for the datatype "bool".
   o Constructor identifiers: "is_true" and "is_false".
   o Characterizing theorems: "true_or_false"; "true_not_false"
*)

Inductive [bool: SET] Theorems Constructors [true: bool][false:bool];
(*

$[bool: SET];
$[true: bool] 
$[false:bool]

$[bool_elim : {T:bool->TYPE}(T true)->(T false)->{b:bool}T b];

[[T:bool->TYPE][true_:T true][false_:T false]
       bool_elim T true_ false_ true  ==> true_
    || bool_elim T true_ false_ false ==> false_];
*)
[    bool_rec = [T|TYPE]bool_elim ([_:bool]T)
            : {T|TYPE}T->T->bool->T 
]
[    bool_ind = [P:bool->Prop]bool_elim P
            : {P:bool->Prop}(P true)->(P false)->{b:bool}P b 
];

Goal bool_double_elim : {T:bool->bool->TYPE}
     (T true true)->(T true false)->(T false true)->(T false false)->
     {x,y:bool}T x y;
intros _____; Refine bool_elim [x:bool]{y:bool}T x y;
Refine bool_elim [y:bool]T true y; Immed;
Refine bool_elim [y:bool]T false y; Immed;
Save bool_double_elim;     

[    is_true = [b:bool] Eq b true
            : bool->Prop 
];
[    is_false = [b:bool] Eq b false
            : bool->Prop 
];

Goal true_not_false : not (Eq true false);
Intros h;  
[isT = bool_elim ([_:bool]Prop) trueProp absurd];
Equiv isT false; Qrepl (Eq_sym h); Refine PropId;
Save true_not_false;


Goal true_or_false : {b:bool}or (is_true b) (is_false b);
Refine bool_elim [b:bool]or (is_true b) (is_false b);
Refine inl; Refine Eq_refl;
Refine inr; Refine Eq_refl;
Save true_or_false;


