Module lib_list_length Import lib_list_basics lib_nat_Lt;

[    length = [s|SET]list_iter zero ([_:s] suc)
            : {s|SET}(list s)->nat 
]
[    nth = [n:nat][t|SET][l:list t][x:t]
           [z [k:list t] = hd x k]
           [s [_:nat][f:(list t)->t][k:list t] = f (tail k)]
           nat_rec z s n l
            : nat->{t|SET}(list t)->t->t 
]
[    build_list (* build list of given length with given member *)
                = [s|SET][f:nat->s] nat_rec (nil s) ([k:nat]cons (f k))
            : {s|SET}(nat->s)->nat->list s
];

Goal list_length_induction : {t|SET}{P:(list t)->Prop}
     {ih:{l:list t}({x:list t}(Lt (length x) (length l))->(P x))->P l}
     {k:list t}P k;
 intros;
 Refine well_founded_induction (length|t) P ih;
Save list_length_induction;

[s,t|SET];

Goal length_zero_nil : {l:list s}(Eq (length l) zero)->(Eq l (nil s));
intros _;
Refine list_ind[l:list s](Eq (length l) zero)->(Eq l (nil s));
intros;
Refine Eq_refl;
intros;
Refine zero_not_suc ? (Eq_sym H1);
Save length_zero_nil;

Goal length_map : {l:list s}{f:s->t}Eq (length (map f l)) (length l);
intros;
Refine list_ind [l:list s]Eq (length (map f l)) (length l);
Refine Eq_refl;
intros __;
Refine Eq_resp suc;
Save length_map;

Goal length_build_list : {f:nat->s}{n:nat}Eq (length (build_list f n)) n;
intros;
Refine nat_ind[n:nat]Eq (length (build_list f n)) n;
Refine Eq_refl;
intros _;
Refine Eq_resp suc;
Save length_build_list;

Goal length_append : {l1,l2:list s}Eq (length (append l1 l2)) (plus (length l1) (length l2));
intros;
Refine list_ind[l1:list s]
    Eq (length (append l1 l2)) (plus (length l1) (length l2));
Refine Eq_refl;
intros __;
Refine Eq_resp suc;
Save length_append;

Discharge s;
