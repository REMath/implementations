(*begin @*)
(***********************************)
(* Author: Zhaohui Luo             *)
(* Email: Zhaohui.Luo@durham.ac.uk *)
(***********************************)

Module lib_setoid Import parameters;

Record [Setoid:SET]
Fields [dom:SET]
       [eq1:dom->dom->Prop];
[Setoid_eq [S|Setoid] = eq1 S];

(*@
end*)
