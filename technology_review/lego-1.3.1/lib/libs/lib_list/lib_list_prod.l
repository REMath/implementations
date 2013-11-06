Module lib_list_prod Import lib_list_length
                            lib_list_bool
                            lib_prod;

(* Contents
   --------
   o Prod product of a pair of lists
   o Theorem about length of prod product
*)


[ assoc [A,B|SET][eq:A->bool][dummy:B][abs:list (prod A B)] : B
      =  foldright ([x:(prod A B)][rest:B]
       if (eq (Fst x)) (Snd x) rest) abs dummy];

[lib_list_dom [A,B|SET] : (list (prod A B))->(list A) = map (Fst|A|B)];
[cod [A,B|SET] : (list (prod A B))->(list B) = map (Snd|A|B)];
[zip [A,B|SET][as:list A][bs:list B] : list (prod A B)
    = foldright ([a:A][_:(list B)->list (prod A B)]map (Pair a))
                  as ([_:list B]nil (prod A B)) bs];
                
[s,t|SET]

[    prod_list = [l1:list s][l2:list t]list_iter (nil (prod s t)) 
                  ([a:s]append (map (Pair a) l2)) l1
            : (list s)->(list t)->list (prod s t)
];

Goal length_prod : {l1:list s}{l2:list t}
     Eq (length (prod_list l1 l2)) (times (length l1) (length l2));
intros;
Refine list_ind
     [l1:list s]Eq (length (prod_list l1 l2)) (times (length l1) (length l2));
Refine Eq_refl;
intros __;
Qrepl length_append (map (Pair x) l2) (prod_list l l2);
Qrepl length_map l2 (Pair x);
Refine Eq_resp (plus (length l2));
Save length_prod;

Discharge s;










