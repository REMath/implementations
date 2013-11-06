Module lib_list_partial Import lib_list_bool
                               lib_unit
                               lib_sum;



[    head = (* "in1 void" is returned when applied to nil *)
            [t|SET]
              list_iter(in1|unit|t void) ([x:t][_:sum unit t]in2|unit|t x)
            : {t|SET}(list t)->sum unit t 
]

[    last = [s|SET]list_rec
                       (in1|unit|s void)
                       ([x:s][l:list s][prev:(sum unit s)]
                              if (nil_test l) (in2 x) prev)
            : {s|SET}(list s)->sum unit s 
]
[    prune = [s|SET]list_rec
                       (in1|unit|(list s) void)
                       ([x:s][l:list s][prune_l:sum unit (list s)]
                            if (nil_test l) 
                               (in2 (nil s))
                               (case
                                   ([_:unit] in1 void)
                                   ([l:list s] in2 (cons x l))
                                   prune_l))
            : {s|SET}(list s)->sum unit (list s)
]
[t|SET];


Goal last_resp_cons : {l:list t}{a,b:t}(Eq (last (cons a l)) (last (cons b (cons a l))));
Refine list_ind [l:list t]{a,b:t}Eq (last (cons a l)) (last (cons b (cons a l)));
intros;
Refine Eq_refl;
intros;
Qrepl Eq_sym (H x a);
Refine Eq_refl;
Save last_resp_cons;

Goal last_resp_append : {l,m:list t}{a:t}(Eq (last (append l (cons a m))) (last (cons a m)));
intros;
Refine list_ind [l:list t]Eq (last (append l (cons a m))) (last (cons a m));
Refine Eq_refl;
intros;
Equiv Eq (last (cons ? (append ? ?))) ?;
Equiv Eq (if ? ? (last (append l1 (cons a m)))) ?;
Qrepl nil_test_on_append l1 m a;
Refine H;
Save last_resp_append;

Goal last_gives_last : {l:list t}{a:t}(Eq (last (append l (cons a (nil t)))) (in2 a));
intros;
Refine list_ind [l:list t]Eq (last (append l (cons a (nil t)))) (in2 a);
Refine Eq_refl;
intros;
Equiv Eq (last (cons ? (append ? ?))) ?;
Equiv Eq (if ? ? (last (append l1 (cons a ?)))) ?;
Qrepl nil_test_on_append l1 (nil t) a;
Refine H;
Save last_gives_last;

Goal prune_resp_cons : {l:list t}{a,b:t}
(Eq (prune (cons b (cons a l))) (case ([_:unit](in1 void) )
           ([l:list t](in2 (cons b l))) (prune (cons a l))));
Refine list_ind [l:list t]{a,b:t}(Eq (prune (cons b (cons a l))) (case ([_:unit](in1 void) )
           ([l:list t](in2 (cons b l))) (prune (cons a l))));
intros;
Refine Eq_refl;
intros;
Qrepl Eq_sym (H x a);
Refine Eq_refl;
Save prune_resp_cons;

Goal prune_non_empty_is_list : {l:list t}{a:t}Ex([m:list t](Eq (prune (cons a l)) (in2 m)));
Refine list_ind [l:list t]{a:t}Ex ([m:list t]Eq (prune (cons a l)) (in2 m));
intros;
Refine ExIntro;
Refine +1 Eq_refl;
intros;
Refine H x;
intros;
Refine ExIntro;
Refine cons a t1;
Equiv Eq  (case ([_:unit] in1 void) ([l:list t] in2 (cons a l))
(prune (cons x l))) ?;
Qrepl H1;
Refine Eq_refl;
Save prune_non_empty_is_list;

Goal prune_resp_append : {l,m:list t}{a:t}(Eq (prune (append l (cons a m))) 
(case ([_:unit](in1 void) )
      ([x:list t](in2 (append l x))) (prune (cons a m))));
intros;
Refine list_ind [l:list t]Eq (prune (append l (cons a m))) (case ([_:unit]in1 void) ([x:list t]in2 (append l x)) (prune (cons a m)));
Refine prune_non_empty_is_list m a;
intros;
Qrepl H;
Refine Eq_refl;
intros;
Refine prune_non_empty_is_list m a;
intros;
Qrepl H1;
Equiv Eq (prune (append (cons x l1) (cons a m))) (in2 (append (cons x l1) t1));
Equiv Eq (if|(sum unit (list t)) ? ? (case ? ? (prune (append l1 (cons a m))))) ?;
Qrepl nil_test_on_append l1 m a;
Qrepl H;
Qrepl H1;
Equiv Eq (in2 ?) ?;
Refine Eq_refl;
Save prune_resp_append;
(* Universes: constant limits headroom...not any more ?? *)

Goal prune_deletes_tip : {x:t}{l:list t}(Eq (prune (append l (cons x (nil t)))) (in2 l));
intros _;
Refine list_ind [l:list t]Eq (prune (append l (cons x (nil t)))) (in2 l);
Refine Eq_refl;
intros;
Equiv Eq (if|(sum unit (list t)) (nil_test (append ? ?)) ? (case ? ? (prune (append ? ?)))) ?;
Qrepl H;
Qrepl nil_test_on_append l (nil t) x;
Refine Eq_refl;
Save prune_deletes_tip;

Discharge t;
