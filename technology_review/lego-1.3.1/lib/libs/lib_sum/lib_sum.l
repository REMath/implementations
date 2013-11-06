Module lib_sum Import lib_eq_basics;

(* Contents
   --------
   o Definition and induction principles for the "sum" datatype.
   o Constructor identifiers: "is_in1" and "is_in2".
   o Some theorems
*)

Inductive [sum:SET] ElimOver TYPE Double
Parameters [A,B:SET]
Constructors [in1_exp:A->sum][in2_exp:B->sum];
Discharge A;
in1 == [s,t|SET]in1_exp s t;

in2 == [s,t|SET]in2_exp s t;
(*
$[sum: SET->SET->SET]
$[in1 : {s,t|SET}s->(sum s t)]
$[in2 : {s,t|SET}t->(sum s t)]
$[sum_elim : {s,t|SET}
             {T:(sum s t)->TYPE}
             ({x:s}T (in1 x))->({y:t}T (in2 y))->
                                   ({z:sum s t}T z)];

[[s,t|SET]
 [T:(sum s t)->TYPE]
 [f:{x:s}T (in1 x)]
 [g:{y:t}T (in2 y)]
 [x:s]
 [y:t]
    sum_elim T f g (in1 x) ==> f x
 || sum_elim T f g (in2 y) ==> g y];
*)
[    case = [s,t|SET][u|TYPE]sum_elim s t ([_:sum s t]u)
          : {s,t|SET}{u|TYPE}(s->u)->(t->u)->(sum s t)->u 
]
[    sum_ind = [s,t|SET][P:(sum s t)->Prop]sum_elim s t P
          : {s,t|SET}
            {P:(sum s t)->Prop}
            ({x:s}P (in1 x))->({y:t}P (in2 y))->
                                      {z:sum s t}P z 
]
[    is_in1 = [s,t|SET][x:sum s t] Ex[y:s]Eq (in1 y) x
          : {s,t|SET}(sum s t)->Prop
]
[    is_in2 = [s,t|SET][x:sum s t] Ex[y:t]Eq (in2 y) x
          : {s,t|SET}(sum s t)->Prop
];


Goal in1_or_in2 : {s,t|SET}{x:sum s t}or (is_in1 x) (is_in2 x);
        intros s t;
        Refine sum_ind [x:sum s t]or (is_in1 x) (is_in2 x);
        intros x; Refine inl; exI ?; Refine x; Refine Eq_refl;
        intros y; Refine inr; exI ?; Refine y; Refine Eq_refl;
Save in1_or_in2;


Goal in1_not_in2 : {s,t|SET}{x|s} not (is_in2 (in1|s|t x));
        Intros s t x h; exE h; intros t1 h1;
        [IsIn1 = case ([_:s]trueProp) ([_:t]absurd)];
        Equiv IsIn1 (in2 t1); Qrepl h1; Refine PropId;
Save in1_not_in2;
       


Goal in2_not_in1 : {s,t|SET}{x|t} not (is_in1 (in2|s|t x)); 
        Intros s t x h; exE h; intros t1 h1;
        [IsIn1 = case ([_:s]absurd) ([_:t]trueProp)];
        Equiv IsIn1 (in1 t1); Qrepl h1; Refine PropId;
Save in2_not_in1;


Goal in1_inj : {s,t|SET}{x,y:s}(Eq (in1|s|t x) (in1|s|t y))->Eq x y;
        intros; 
        Refine Eq_subst H (case ([x':s]Eq x x') ([_:t]absurd)) (Eq_refl x);
Save in1_inj;


Goal in2_inj : {s,t|SET}{x,y:t}(Eq (in2|s|t x) (in2|s|t y))->Eq x y;
        intros;
        Refine Eq_subst H (case ([_:s]absurd) ([y':t]Eq x y')) (Eq_refl x);
Save in2_inj; 









