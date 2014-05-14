Module lib_unit Import lib_eq_basics;

(* Contents
   --------
   o Definition and elimination rules for the unit type.
   o Constructor identifier: is_void
*)

Inductive [unit:SET] ElimOver TYPE 
Constructors [void:unit];
(*
$[unit:SET];
$[void:unit];

$[unit_elim : {T:unit->TYPE}(T void)->{u:unit} T u];

[[T:unit->TYPE]
 [x:T void]
    unit_elim T x void ==> x];
*)
[    unit_rec = [t|TYPE]unit_elim ([_:unit]t)
              : {t|TYPE}t->unit->t 
]
[    unit_ind = [P:unit->Prop]unit_elim P
              : {P:unit->Prop}(P void)->{u:unit}P u 
]
[    is_void = [x:unit]Eq void x
];


Goal all_units_void : {x:unit}is_void x;
Refine unit_ind [x:unit]is_void x;
Refine Eq_refl;
Save all_units_void;

Goal all_units_same : {x,y:unit}Eq x y;
intros; Refine Eq_trans; Refine void;
Refine Eq_sym; Refine all_units_void;
Refine all_units_void;
Save all_units_same;



