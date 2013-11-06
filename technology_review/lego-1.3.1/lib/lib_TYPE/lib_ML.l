(* Time-stamp: <18 May 95 tms ~tms/lego/lib_ML.l> *)

Module lib_ML Import lib_empty lib_unit lib_bool;

Goal absurd_impl_empty: absurd -> empty;
intros;
Equiv bool_elim ([_:bool]SET) empty unit true;
Claim Eq true false; Qrepl ?+1;
Refine void; Immed;
Save;


