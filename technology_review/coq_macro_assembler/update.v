(* Class for functional update notation *)
Class UpdateOps M K V := update: M -> K -> V -> M.

Bind Scope update_scope with update.
Notation "m '!' d := x" := (update m d x) (left associativity, at level 189) : update_scope.

Local Open Scope update_scope.
Class Update M K V {ops: UpdateOps M K V} :=
{ update_same m k v w : (m !k:=v !k:=w) = (m !k:=w)
; update_diff m k l v w : k<>l -> (m !k:=v !l:=w) = (m !l:=w !k:=v)
}. 


