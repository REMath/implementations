Module lib_list_bool Import lib_list_basics lib_bool_thms;


[    nil_test = [s|Type]list_iter true [_:s][_:bool]false
            : {s|Type}(list s)->bool 
]
[    exist_list (* decide whether a list has a member with a given property *)
                = [t|Type][P:t->bool]
                      list_iter false ([x:t][b:bool]orelse (P x) b)
            : {t|Type}(t->bool)->(list t)->bool 
]
[    all_list (* decide whether all members have a given property *)
              = [t|Type][P:t->bool]list_iter true ([x:t][b:bool]andalso (P x) b)
            : {t|Type}(t->bool)->(list t)->bool 
]
[    member = [t|Type][eq:t->t->bool][x:t]exist_list (eq x)
            : {t|Type}(t->t->bool)->t->(list t)->bool 
]
[    list_eq = [t|Type][eq:t->t->bool]
                list_rec
                   (list_iter true ([_:t][_:bool]false))
                   ([hd:t][tl:list t][eq_tl:(list t)->bool]
                      list_rec false
                              ([hd':t][tl':list t][_:bool]
                                  (andalso (eq hd hd') (eq_tl tl'))))
            : {t|Type}(t->t->bool)->(list t)->(list t)->bool 
]
[    del_first (* delete first occurence of an item in a list *)
               = [t|Type][eq:t->t->bool][x:t] 
                   list_rec 
                     (nil t)
                     ([hd:t][tl:list t][prev:list t] 
                         if (eq x hd) tl (cons hd prev))
            : {t|Type}(t->t->bool)->t->(list t)->list t 
]
[    del_all = (* delete all occurences of an item in a list *)
         [t|Type][eq:t->t->bool][x:t]
           list_iter
              (nil t)
              ([hd:t][prev:list t]
                  if (eq x hd) prev (cons hd prev))
            : {t|Type}(t->t->bool)->t->(list t)->list t 
]
[list_sub [A,B|Type][eq:A->bool][a:A] : (list A)->(list A) 
       = map ([b:A]if (eq b) a b)];
Goal exist_list_append_lem : {t|Type}{P:t->bool}{j,k:list t}
        Eq (exist_list P (append j k))
          (orelse (exist_list P  j) (exist_list P k));
intros;
Refine list_ind [j:list t]Eq (exist_list P (append j k))
                     (orelse (exist_list P j) (exist_list P k));
Refine Eq_refl;
intros;
Equiv Eq (orelse (P x) (exist_list P (append l k)))
        (orelse (orelse (P x) (exist_list P l)) ?);

Qrepl orelse_assoc (P x) (exist_list P l) (exist_list P k);
Qrepl H; Refine Eq_refl;
Save exist_list_append_lem;

Goal member_append_lem : {t|Type}{eq_on_t:t->t->bool}{x:t}{j,k:list t}
        Eq (member eq_on_t x (append j k))
          (orelse (member eq_on_t x j) (member eq_on_t x k));
intros; Refine exist_list_append_lem (eq_on_t x) j k;
Save member_append_lem;

[t|Type];

Goal nil_test_true_equiv_Eq_nil : {l:list t}iff (Eq (nil_test l) true) (Eq l (nil t));
Refine list_ind [l:list t]iff (Eq (nil_test l) true) (Eq l (nil t));
Refine pair;
intros; Refine Eq_refl;
intros; Refine Eq_refl;
intros;
Refine pair;
intros;
Refine true_not_false;
Refine Eq_sym H1;
intros;
Refine nil_not_cons;
Refine +3 Eq_sym H1;
Save nil_test_true_equiv_Eq_nil;

Goal nil_test_false_equiv_Eq_cons : {l:list t}iff (Eq (nil_test l) false) (Ex([a:t]Ex([m:list t]
        (Eq l (cons a m)))));
Refine list_ind [l:list t]iff (Eq (nil_test l) false) (Ex([a:t]Ex([m:list t]
        (Eq l (cons a m)))));
Refine pair;
intros;
Refine true_not_false;
Refine H;
intros;
Refine H; intros;
Refine H1; intros;
Refine nil_not_cons ? ? H2;
intros;
Refine pair;
intros;
Refine ExIntro;
Refine +1 ExIntro;
Refine +2 Eq_refl;
intros;
Refine Eq_refl;
Save nil_test_false_equiv_Eq_cons;

Goal nil_test_on_append : {l,m:list t}{a:t}Eq (nil_test (append l (cons a m))) false;
intros;
Refine list_ind [l:list t](Eq (nil_test (append l (cons a m))) false);
Refine Eq_refl;
intros;
Refine Eq_refl;
Save nil_test_on_append;

Discharge t;
