Module lib_empty Import parameters;

(* Contents
   --------
   o Definition and induction principles for the datatype "empty"
*)
echo "Searching for definition of SET, TYPE";

SET; TYPE;

Inductive [empty:SET] Constructors NoReductions;

[empty_rec [t|TYPE] = empty_elim ([_:empty]t)];

[empty_ind [P:empty->Prop] = empty_elim P];
