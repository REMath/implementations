Module lib_sum Import lib_bool lib_eq_basics;

(* Contents
   --------
   o Definition and induction principles for the "sum" datatype.
   o Constructor identifiers: "is_in1" and "is_in2".
   o Some theorems
*)

Inductive [sum:SET] ElimOver TYPE Parameters [A,B:SET]
Constructors [in1_exp:A->sum][in2_exp:B->sum];
Discharge A;

in1 == [s,t|SET]in1_exp s t;

in2 == [s,t|SET]in2_exp s t;
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

Goal in1_inj : {s,t|SET}{x,y:s}(Eq (in1|s|t x) (in1|s|t y))->Eq x y;
        intros; 
Refine Eq_resp (case ([x:s]x) ([x:t]y)) H;
Save in1_inj;

Goal in2_inj : {s,t|SET}{x,y:t}(Eq (in2|s|t x) (in2|s|t y))->Eq x y;
        intros;
Refine Eq_resp (case ([x:s]y) ([x:t]x)) H;
Save in2_inj; 

Goal in1_not_in2 : {s,t|SET}{x|s} not (is_in2 (in1|s|t x)); 
        Intros s t x h; exE h; intros t1 h1;
Refine true_not_false;
Refine Eq_resp (case ([_:s]false) ([_:t]true)) h1;
Save in1_not_in2;

Goal in2_not_in1 : {s,t|SET}{x|t} not (is_in1 (in2|s|t x)); 
        Intros s t x h; exE h; intros t1 h1;
Refine true_not_false;
Refine Eq_resp (case ([_:s]true) ([_:t]false)) h1;
Save in2_not_in1;






