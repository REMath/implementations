Module lib_list Import lib_eq_basics;

(* Contents
   --------
   o Definition and induction principles for the datatype "list" of 
     polymorphic lists.
   o Constructor identifiers: "is_nil" and "is_cons".
   o Characterizing theorems: "nil_or_cons" and "nil_not_cons".
*)

Inductive [list:Type] Parameters [t?Type] ElimOver Type
Constructors [nil:list][cons:t->list->list];

Discharge t;

[cons1 [t:Type][x:t][l:list t]= cons x l];

(*
$[list : Type->Type];

$[nil:{t:Type}list t]
$[cons:{t|Type}t->(list t)->(list t)];

$[list_elim : {t|Type}
          {T:(list t)->Type}
          (T (nil t))->
          ({x:t}{l:list t}(T l)->(T (cons x l)))->
                                         {l:list t}T l];

[[t:Type]
 [T:(list t)->Type]
 [nil_case:T(nil t)]
 [cons_case:{x:t}{l:list t}(T l)->(T (cons x l))]
 [x:t]
 [l:list t]
    list_elim nil_case cons_case (nil t) ==> nil_case
 || list_elim nil_case cons_case (cons x l) ==> 
                            cons_case x l (list_elim nil_case cons_case l)];
*)

[    list_rec = [s|Type][t|Type]list_elim|s [_:list s]t
            :  {s|Type}{t|Type}t->(s->(list s)->t->t)->(list s)->t 
]
[    list_iter = [s|Type][t|Type][x:t][f:s->t->t]list_rec x ([y:s][_:list s]f y)
            : {s|Type}{t|Type}t->(s->t->t)->(list s)->t 
]
[    list_ind = [s|Type][P:(list s)->Prop]list_elim|s P
            : {s|Type}{P:(list s)->Prop}
                     (P (nil s))->
                     ({x:s}{l:list s}(P l)->P (cons x l))->
                        {l:list s}P l 
];

Goal list_double_elim : {s|Type}{T:(list s)->(list s)->Type}
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

[    is_nil = [t|Type][l:list t]Eq (nil t) l
            : {t|Type}(list t)->Prop
]
[    is_cons = [t|Type][l:list t]Ex[x:t]Ex[l':list t] Eq (cons x l') l
            : {t|Type}(list t)->Prop
];

Goal nil_or_cons : {t|Type}{l:list t} or (is_nil l) (is_cons l);
Intros t; Refine list_ind [l:list t] or (is_nil l) (is_cons l);
Refine inl; Expand is_nil; Refine Eq_refl;
Intros x l H; Refine inr;
exI?; Refine x; exI?; Refine l; Refine Eq_refl;
Save nil_or_cons;


Goal nil_not_cons : {t|Type}{l:list t}{x:t} not (Eq (nil t) (cons x l));
Intros t l x H;
[isT = list_iter trueProp ([_:t][_:Prop]absurd)];
Equiv isT (cons x l); Qrepl (Eq_sym H); Refine PropId;
Save nil_not_cons;




