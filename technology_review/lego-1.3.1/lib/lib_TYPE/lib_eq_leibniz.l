Module lib_eq_leibniz Import lib_logic;

(* Contents
   --------
   o Definition and rules for manipulating Leibniz equality.

   Credit
   ------
   Randy Pollack
*)

echo "Searching for definition of SET, TYPE";

SET; TYPE;

[T,S,U|SET];

[     Eq = [x,y:T]{P:T->Prop}(P x)->P y
          : T->T->Prop 
] 

[     Eq_refl = [t:T][P:T->Prop][h:P t]h
          : refl Eq
];

Goal Eq_subst : {x,y|T}(Eq x y)->{P:T->Prop}(P x)->P y;
 Intros x y H P H1;
 Refine H P H1;
Save Eq_subst;

Discharge T;







