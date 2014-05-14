Module lib_empty Import parameters;

(* Contents
   --------
   o Definition and induction principles for the datatype "empty"
*)
echo "Searching for definition of Type, Type";

Type; Type;

Inductive [empty:Type] Constructors NoReductions;

[empty_rec [t|Type] = empty_elim ([_:empty]t)];

[empty_ind [P:empty->Prop] = empty_elim P];
