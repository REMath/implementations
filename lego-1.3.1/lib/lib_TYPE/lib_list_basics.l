Module lib_list_basics Import lib_list;

(* List basics, which don't require any other datatypes *)



[    singleton = [t|Type][x:t]cons x (nil t)
            : {t|Type}t->list t 
]
[    hd = (* given default value is returned when applied to nil *)
          [t|Type][x:t][l:list t]list_iter x ([h:t][_:t]h) l
            : {t|Type}t->(list t)->t 
]

[    tail = [t|Type]list_rec (nil t) ([_:t][l,_:list t]l)
            : {t|Type}(list t)->list t 
]
[    fold = [s|Type][t|Type][f:t->s->t][start:t]list_iter start [x:s][y:t]f y x
            : {s|Type}{t|Type}(t->s->t)->t->(list s)->t 
]
[ foldright = [B|Type][A|Type][g:A->B->B][l:list A][b:B]
              list_iter b ([a:A][b:B]g a b) l
];
[foldleft  = [B|Type][A|Type][g:A->B->B]
             list_iter ([b:B]b) ([a:A][f:B->B][b:B]f (g a b))
];
[    map = [s,t|Type][f:s->t]list_iter (nil t) ([x:s] cons (f x))
            : {s,t|Type}(s->t)->(list s)->list t 
]
[    append = [t|Type][l,l':list t]list_iter l' (cons|t) l
            : {t|Type}(list t)->(list t)->list t 
]
[    tack = [t|Type][x:t][l:list t]append l (cons x (nil t))
            : {t|Type}t->(list t)->list t 
]
[    reverse = [t|Type]list_iter (nil t) (tack|t)
            : {t|Type}(list t)->list t 
]
[    flatten [t|Type] = fold (append|t) (nil|t)
]

[cons_injective = [t|Type][k,l|list t][x,y|t][h:Eq (cons x k) (cons y l)]
                                     Eq_resp|(list t)|(list t) (tail|t) h
     : {t|Type}{k,l|list t}{x,y|t}(Eq (cons x k) (cons y l))->
                                     Eq (tail (cons x k)) (tail (cons y l)) 
];
Goal cons_inj : {s|Type}{a,b|s}{xs,ys|list s}(Eq (cons a xs) (cons b ys))->
     ((Eq a b) /\ (Eq xs ys));
intros;
Refine pair;
Refine Eq_resp (hd a) H;
Refine Eq_resp (tail|s) H;
Save cons_inj;

Goal l_not_cons_l : {t|Type}{l:list t}{x:t}not (Eq l (cons x l));
intros _; Refine list_ind [l:list t]{x:t}not (Eq l (cons x l));
intros; Refine nil_not_cons;
Intros _____; Refine H x;   
Refine cons_injective; Refine +2 H1;
Save l_not_cons_l;


Goal append_cons : {t|Type}{k,l:list t}{x:t}
        Ex2 [y:t][j:list t]Eq (append k (cons x l)) (cons y j); 
intros;
Refine list_ind [k:list t]Ex2 ([y:t][j:list t]
                   Eq (append k (cons x l)) (cons y j));
Refine Ex2Intro; Refine x; Refine l; Refine Eq_refl;
intros; Refine Ex2Intro; Refine x1; Refine append l1 (cons x l);
Refine Eq_refl;
Save append_cons; 


Goal nil_not_append_cons : {t|Type}{x:t}{k,l:list t}not (Eq (nil t) (append k (cons x l)));
intros; Refine append_cons k l x; intros;
Qrepl H; Refine nil_not_cons;
Save nil_not_append_cons;


Goal append_assoc : {t|Type}{j,k,l:list t}Eq (append j (append k l))
                             (append (append j k) l);
intros _;
Refine list_ind [j:list t]{k,l:list t}Eq (append j (append k l))
                              (append (append j k) l);
intros; Refine Eq_refl;
intros;
Equiv Eq (cons x (append l (append k l1)))
        (cons x (append (append l k) l1));
Qrepl H k l1; Refine Eq_refl;
Save append_assoc;

[s,t|Type];

Goal append_nil : {l:list t}(Eq (append l (nil t)) l);
Refine list_ind [l:list t](Eq (append l (nil t)) l);
Refine Eq_refl;
intros;
Equiv Eq (cons x (append l (nil t))) (cons x l);
Refine Eq_resp;
Immed;
Save append_nil;

Goal append_reverse : {l,m:list t}(Eq (reverse (append l m)) 
                     (append (reverse m) (reverse l)));
intros l m;
Refine list_ind [l:list t]((Eq (reverse (append l m)) (append (reverse m) (reverse l))));
Qrepl append_nil (reverse m);
Refine Eq_refl;
intros;
Equiv Eq  (tack x (reverse (append l1 m))) ?;
Equiv Eq ? (append (reverse m) (append (reverse  l1) (cons x (nil t))));
Qrepl append_assoc (reverse m) (reverse l1) (cons x (nil t));
Qrepl H;
Refine Eq_refl;
Save append_reverse;


[a:t][k,l:list t];

Goal append_strict : (Eq (append k l) (nil ?)) -> and (Eq k (nil ?)) (Eq l (nil ?));
intros;
Refine list_elim [k|list ?](Eq (append k l) (nil ?)) -> 
		   and (Eq k (nil ?)) (Eq l (nil ?));

  (* base case *)
  intros;
  andI;
  Refine Eq_refl;
  Immed;

  (* induction step *)
  intros; 
  Refine nil_not_cons;
  Refine +3 Eq_sym H1;

Immed;
Save append_strict; Discharge a;

Goal double_reverse_is_identity : {l:list t}Eq (reverse (reverse l)) l;
Refine list_ind [l:list t](Eq (reverse (reverse l)) l);
Refine Eq_refl;
intros;
Equiv Eq (reverse (append (reverse l) ?)) ?;
Qrepl append_reverse (reverse l) (cons x (nil t));
Qrepl H;
Refine Eq_refl;
Save double_reverse_is_identity;

Goal foldright_append_lem : {g:s->t->t}{G,H:list s}{b:t}
   Eq (foldright g (append G H) b) (foldright g G (foldright g H b));
Intros g;
Refine list_ind [G:list s]{H:list s}{b:t}
           Eq (foldright g (append G H) b) (foldright g G (foldright g H b));
intros; Refine Eq_refl;
intros;
Equiv Eq (g x (foldright g (append l H1) b))
        (g x (foldright g l (foldright g H1 b)));
Qrepl H H1 b;Refine Eq_refl;
Save foldright_append_lem;

Goal foldleft_append_lem : {g:s->t->t}{G,H:list s}{b:t}
    Eq (foldleft g (append G H) b) (foldleft g H (foldleft g G b));
Intros g;
Refine list_ind [G:list s]{H:list s}{b:t}
              Eq (foldleft g (append G H) b) (foldleft g H (foldleft g G b));
intros; Refine Eq_refl;
intros;
Equiv Eq (foldleft g (append l H1) (g x b))
        (foldleft g H1 (foldleft g l (g x b)));
Qrepl H H1 (g x b);Refine Eq_refl;
Save foldleft_append_lem;

Discharge s;



