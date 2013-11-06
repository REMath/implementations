Module lib_list Import lib_eq_basics;

(* Contents
   --------
   o Definition and induction principles for the datatype "list" of 
     polymorphic lists.
   o Constructor identifiers: "is_nil" and "is_cons".
   o Characterizing theorems: "nil_or_cons" and "nil_not_cons".
*)

Inductive [list:SET] Parameters [t?SET] ElimOver TYPE
Constructors [nil:list][cons:t->list->list];

Discharge t;

[cons1 [t:SET][x:t][l:list t]= cons x l];

(*
$[list : SET->SET];

$[nil:{t:SET}list t]
$[cons:{t|SET}t->(list t)->(list t)];

$[list_elim : {t|SET}
          {T:(list t)->TYPE}
          (T (nil t))->
          ({x:t}{l:list t}(T l)->(T (cons x l)))->
                                         {l:list t}T l];

[[t:SET]
 [T:(list t)->TYPE]
 [nil_case:T(nil t)]
 [cons_case:{x:t}{l:list t}(T l)->(T (cons x l))]
 [x:t]
 [l:list t]
    list_elim nil_case cons_case (nil t) ==> nil_case
 || list_elim nil_case cons_case (cons x l) ==> 
                            cons_case x l (list_elim nil_case cons_case l)];
*)

[    list_rec = [s|SET][t|TYPE]list_elim|s [_:list s]t
            :  {s|SET}{t|TYPE}t->(s->(list s)->t->t)->(list s)->t 
]
[    list_iter = [s|SET][t|TYPE][x:t][f:s->t->t]list_rec x ([y:s][_:list s]f y)
            : {s|SET}{t|TYPE}t->(s->t->t)->(list s)->t 
]
[    list_ind = [s|SET][P:(list s)->Prop]list_elim|s P
            : {s|SET}{P:(list s)->Prop}
                     (P (nil s))->
                     ({x:s}{l:list s}(P l)->P (cons x l))->
                        {l:list s}P l 
];

Goal list_double_elim : {s|SET}{T:(list s)->(list s)->TYPE}
     (T (nil s) (nil s))->
     ({x:s}{l:list s}(T (nil s) l)->T (nil s) (cons x l))->
     ({x:s}{l:list s}({l':list s}T l l')->T (cons x l) (nil s))->
     ({x:s}{l:list s}({l':list s}T l l')->{y:s}{l':list s}(T (cons x l) l')->
                    T (cons x l) (cons y l'))->
     {l,l':list s}T l l';
intros s T bb bs sb ss; Refine list_elim [l:list s]{l':list s}T l l';
Refine list_elim (T (nil s)); Immed;
intros b x h; Refine list_elim (T (cons b x));
Refine sb b x h; Refine ss b x h;
Save list_double_elim;

[    is_nil = [t|SET][l:list t]Eq (nil t) l
            : {t|SET}(list t)->Prop
]
[    is_cons = [t|SET][l:list t]Ex[x:t]Ex[l':list t] Eq (cons x l') l
            : {t|SET}(list t)->Prop
];

Goal nil_or_cons : {t|SET}{l:list t} or (is_nil l) (is_cons l);
Intros t; Refine list_ind [l:list t] or (is_nil l) (is_cons l);
Refine inl; Expand is_nil; Refine Eq_refl;
Intros x l H; Refine inr;
exI?; Refine x; exI?; Refine l; Refine Eq_refl;
Save nil_or_cons;


Goal nil_not_cons : {t|SET}{l:list t}{x:t} not (Eq (nil t) (cons x l));
Intros t l x H;
[isT = list_iter trueProp ([_:t][_:Prop]absurd)];
Equiv isT (cons x l); Qrepl (Eq_sym H); Refine PropId;
Save nil_not_cons;




