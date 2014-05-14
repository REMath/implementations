Module lib_list_misc Import lib_list_length
                            lib_list_partial;


[    same_length = [s,t|Type]list_iter
                              (list_iter true ([_:t][_:bool]false))
                              ([_:s][prev:(list t)->bool]
                                 (list_rec false 
                                          ([_:t][tl:list t][_:bool]prev tl)))
            :{s,t|Type}(list s)->(list t)->bool 
]

[t|Type];

Goal Eq_length_imp_same_length_true : {l,m:list t}(Eq (length l) (length m)) -> is_true (same_length l m);
Refine list_ind [l:list t]{m:list t}(Eq (length l) (length m))->is_true (same_length l m);
Refine list_ind [m:list t](Eq (length (nil t)) (length m))->is_true (same_length (nil t) m);
intros;
Refine Eq_refl;
intros;
Refine true_not_false;
Refine zero_not_suc;
Refine +1 H1;
intros ___;
Refine list_ind [m:list t](Eq (length (cons x l)) (length m))->is_true (same_length (cons x l) m);
intros;
Refine zero_not_suc;
Refine +1 Eq_sym H1;
intros;
Equiv is_true (same_length l l1);
Refine H;
Refine suc_injective;
Refine H2;
Save Eq_length_imp_same_length_true;

Discharge t;
