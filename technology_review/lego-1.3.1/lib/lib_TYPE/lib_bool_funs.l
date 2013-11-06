Module lib_bool_funs Import lib_bool;

(* Contents
   --------
   o Some basic functions that operate on bool
*)

[    if = [t|TYPE][b:bool][tCase,fCase:t] bool_rec tCase fCase b
            : {t|TYPE}bool->t->t->t 
]
[    andalso = [a,b:bool] if a b false
            : bool->bool->bool 
]
[    orelse =  [a,b:bool] if a true b
            : bool->bool->bool 
]
[    inv = [u:bool] if u false true
            : bool->bool 
]
[    implies = [a,b:bool] if b true (if a false true)
            : bool->bool->bool 
]
[    bool_eq = [a,b:bool] if a (if b true false) (if b false true)
            : bool->bool->bool 
];








