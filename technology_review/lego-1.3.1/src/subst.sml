(* subst.sml   object langage substitution *)

(** Substitution of object language (nameless variable) terms **)
(* Remark : We use sharing for the substitution functions *)
fun subst1 a : cnstr->cnstr = 
  let
    fun substrec n : (cnstr -> cnstr modif) = 
      let
	val mem = ref ([]:(int*cnstr)list)
	val closFlg = ref false
        fun mem_lift() = 
	  let val n' = n-1
	  in  if !closFlg then a else assoc n' (!mem)
		   handle _ =>       (* call to lift_unshared tests a closed *)
		     case lift_unshared n' a
		       of UMod => (closFlg:=true; a)           (* closed *)
			| (Mod a') => (mem:= (n',a')::(!mem); a')
	  end
      in
	fn Rel(n')   => if n'=n then Mod(mem_lift())
			else if n'<n then UMod else Mod(Rel(n'-1))
	 | App(b)    => (mkApp (substrec n) b):cnstr modif
	 | try as Bind(b as ((Thry,_),_,_,_)) =>
	     (if not (!theory_debug) then ()
	      else (prs"\n##thry_debug:subst1 in ";legoprint try);
	      mkBind substrec n b)
	 | Bind(b)   => mkBind substrec n b
	 | Tuple(b)  => mkTuple (substrec n) b
	 | CnLst(b)  => mkCnLst (substrec n) b
	 | Proj(c)   => mkProj (substrec n) c
	 | RedTyp(c) => mkRedTyp (substrec n) c
	 | LabVT(b)  => mkLabVT (substrec n) b 
	 | _         => UMod
      end
  in share (substrec 1)
  end;

(* an optimisation: substitution of a closed term *)
fun subst1closed a =
  let fun s1c n = 
    fn Rel(n')  => if n'=n then Mod(a)
		   else if n'<n then UMod else Mod(Rel(n'-1))
     | App(b)   => mkApp (s1c n) b
     | try as Bind(b as ((Thry,_),_,_,_)) =>
	 (if not (!theory_debug) then ()
	  else (prs"\n##thry_debug:subst1closed in ";legoprint try);
	  mkBind s1c n b)
     | Bind(b)  => mkBind s1c n b
     | Tuple(b) => mkTuple (s1c n) b
     | CnLst(b) => mkCnLst (s1c n) b
     | Proj(b)  => mkProj (s1c n) b
     | RedTyp(b)=> mkRedTyp (s1c n) b
     | LabVT(b) => mkLabVT (s1c n) b
     | _        => UMod
  in share (s1c 1) end


(* Substitute Rel(1) for Ref(br) *)
fun subst2 bref = 
  let fun substrec n =
    fn (Ref br)  => if sameRef br bref then Mod(Rel n) else UMod
     | (App b)   => mkApp (substrec n) b
     | try as Bind(b as ((Thry,_),_,_,_)) =>
	 (if not (!theory_debug) then ()
	  else (prs"\n##thry_debug:subst2 in ";legoprint try);
	  mkBind substrec n b)
     | (Bind b)  => mkBind substrec n b
     | (Tuple b) => mkTuple (substrec n) b
     | (CnLst b) => mkCnLst (substrec n) b
     | (Proj b)  => mkProj (substrec n) b
     | (RedTyp b)=> mkRedTyp (substrec n) b
     | (LabVT b) => mkLabVT (substrec n) b
     | Var(n,t)  => if depends bref t
		      then failwith("type of metavar "^makestring n^
				    " not closed")
		    else UMod
     | _         => UMod
  in share (substrec 1) end;
