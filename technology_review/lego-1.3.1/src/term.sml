(* term.sml *)

val theory_debug = ref false;

local              (* timestamp used for equality of bindings *)
  val ts = ref 0
in
  fun timestamp() = (ts:= succ (!ts); !ts)
end;

datatype visSort = Vis | Hid | Def | VBot
datatype bindSort = Lda | Pi | Sig | Let | Thry
type  bindVisSort = bindSort * visSort
datatype projSort = Fst | Snd | Labl of string
datatype prntVisSort = ShowNorm | ShowForce | NoShow | ShowExp
datatype LocGlob = Local | Global
datatype freeze = Froz | UnFroz
type frzLocGlob = freeze * LocGlob
datatype Kind =
  Red
| Bnd
| LabelTag of (string list) * string
| GenTag of (string list)
| Mrk of string * (string list) * time * timer
| Config of string * string * string * string
| StThry of string
datatype label = Name of string | WeakCast | StrongCast | RedPr
datatype instrs = iNrml

fun prVis Vis = ShowNorm 
  | prVis Hid = NoShow
  | prVis Def = bug"prVis: Def"
  | prVis VBot = bug"prVis: VBot";


(** Abstract syntax **)
datatype  cnstr =
    Prop
  | Theory                                  (* the type of theories *)
  | Type of node
  | Ref of binding
  | Rel of int                                         (* variable *)
  | App of (cnstr * (cnstr list)) * (prntVisSort list) (* application *)
  | Bind of binder_data
  | Var of int * cnstr                      (* existential variable *)
  | Tuple of cnstr * (cnstr list)           (* elem of Sig *)
  | Proj of projSort * cnstr
  | LabVT of label * cnstr * cnstr          (* labeled trm:typ pair *)
  | CnLst of cnstr list                     (* for use in Theories *)
  | RedTyp of instrs * cnstr     (* reduce the synthesised type using insts *)
  | Case of cnstr * cnstr        (* case *)
  | Bot
and binding =
    Bd of {kind:Kind, ts:int, 
	   frz:freeze ref, param:LocGlob, deps:string list,
	   bd:binder_data}
withtype binder_data = bindVisSort * string * cnstr * cnstr

fun isLda (Bind((Lda,_),_,_,_)) = true
  | isLda _ = false
fun isPi (Bind((Pi,_),_,_,_)) = true
  | isPi _ = false
fun isSig (Bind((Sig,_),_,_,_)) = true
  | isSig _ = false
fun isThry (Bind((Thry,_),_,_,_)) = true
  | isThry _ = false;
fun isTuple (Tuple _) = true
  | isTuple _ = false;

fun cnstr_size c =
  let
    fun bd_size (_,_,l,r) = 1 + (cnstr_size l) + (cnstr_size r)
    fun cs_size cs = foldl (fn n => fn c => n + 1 + (cnstr_size c)) 0 cs
  in case c
       of Prop => 1
	| Theory => 1
	| Type(_) => 1
	| Ref(Bd{bd=bd,...}) => 1
	| Rel(_) => 1
	| App((f,cs),_) => 1 + (cnstr_size f) + (cs_size cs)
	| Bind(bd) => 1+(bd_size bd)
	| Var(_,c) => 1+(cnstr_size c)
	| Tuple(T,cs) => 1+(cnstr_size T)+(cs_size cs)
	| CnLst(cs) => 1+(cs_size cs)
	| RedTyp(_,c) => 1+(cnstr_size c)
	| Proj(_,c) => 1+(cnstr_size c)
	| LabVT(_,c,d) => 1+(cnstr_size c)+(cnstr_size d)
	| Case(v,bs) => 1+(cnstr_size c)+(cnstr_size bs)
	| Bot => 1
  end

fun ref_body (Bd b) = b
fun ref_ts br = #ts (ref_body br)
fun ref_frz br = #frz (ref_body br)
fun ref_param br = #param (ref_body br)
fun ref_deps br = #deps (ref_body br)
fun ref_kind br = #kind (ref_body br)
fun ref_isRed br = ref_kind br = Red
fun ref_isBnd br = case ref_kind br
                     of Bnd => true | (GenTag _) => true | _ => false
fun ref_isMrk br = case ref_kind br of Mrk _ => true | _ => false
fun ref_isConfig br = case ref_kind br of Config _ => true | _ => false
fun ref_bd br = #bd (ref_body br)
fun ref_red br = if ref_isRed br then #3 (ref_bd br) else bug"ref_red"
fun ref_bind br = fst (#1 (ref_bd br))
fun ref_vis br = snd (#1 (ref_bd br))
fun ref_nam br = #2 (ref_bd br)
fun ref_mrk br = case ref_kind br of Mrk (s,_,_,_) => s | _ => bug"ref_mrk"
fun ref_imports br =
  case ref_kind br of Mrk (_,i,_,_) => i | _ => bug"ref_imports"
fun ref_filtim br =
  case ref_kind br of Mrk (_,_,t,_) => t | _ => bug"ref_filtim"
fun ref_marktim br =
  case ref_kind br of Mrk (_,_,_,t) => t | _ => bug"ref_marktim"
fun ref_config br = case ref_kind br of Config x => x | _ => bug"ref_config"
fun ref_stThry br = case ref_kind br
		      of StThry x => SOME x | _ => NONE
fun ref_vt br = let val (_,_,v,t) = ref_bd br in (v,t) end
fun ref_isDefn br = ref_isBnd br andalso (ref_bind br) = Let
fun ref_isDefnNow br = ref_isDefn br andalso (!(ref_frz br))=UnFroz
fun ref_isDecl br = ref_isBnd br andalso (ref_bind br) <> Let
fun ref_VAL br = #3 (ref_bd br)
fun ref_TYP br = #4 (ref_bd br)
fun ref_val br = if ref_isDefnNow br then ref_VAL br
		 else Ref br
(******
fun ref_val br = if ref_isDefn br then #3 (ref_bd br) else bug"ref_val"
******)
fun ref_typ br = (if ref_isDefn br then #4 else #3) (ref_bd br)
fun sameRef br br' = ref_ts br = ref_ts br'
fun sameNam br nam = ref_nam br = nam
fun sameMrk br mrk = ref_isMrk br andalso ref_mrk br = mrk
fun ref_updat_vt (Bd{ts,frz,param,deps,kind,bd=(bv,nam,_,_)}) (v,t) =
      Bd{ts=ts,frz=frz,param=param,deps=deps,kind=kind,bd=(bv,nam,v,t)};
fun ref_updat_vtdeps (Bd{ts,frz,param,kind,bd=(bv,nam,_,_),...}) (v,t) d =
      Bd{ts=ts,frz=frz,param=param,deps=d,kind=kind,bd=(bv,nam,v,t)};


(* A Type construction function allows sharing storage *)
fun mkTyp nod = 
    let val (Type0,Type1,Type2) =
      (Type(uconst 0),Type(uconst 1),Type(uconst 2))
    in  case nod
	  of Uconst(0) => Type0
	   | Uconst(1) => Type1
	   | Uconst(2) => Type2
	   | _         => Type(nod)
    end;



(* var_occur tests whether object variable Rel(1) occurs
 * free_occur tests for any free obj var occurrance *)
local
  fun occ f =  
    let fun occur_rec p =
      fn Rel(p')        => f(p,p')
       | App((c,cs),_)  => (occur_rec p c) orelse (exists (occur_rec p) cs)
       | Bind(_,_,c,d)  => (occur_rec (succ p) d) orelse (occur_rec p c)
       | Tuple(T,l)     => (occur_rec p T) orelse (exists (occur_rec p) l)
       | CnLst(l)       => exists (occur_rec p) l
       | Proj(_,c)      => occur_rec p c
       | RedTyp(_,c)    => occur_rec p c
       | LabVT(_,v,t)   => (occur_rec p v) orelse (occur_rec p t)
       | Case(v,bs)     => (occur_rec p v) orelse (occur_rec p bs)
       | _              => false
    in occur_rec
    end
in
  val var_occur = occ (op =) 1
  fun varn_occur n = occ (op =) n
  val free_occur = occ (op <) 0
end;
(**************  not in use ****************
val max_occur =
  let fun mo p =
    fn Rel(n)        => n-p
     | App((c,cs),_) => fold max (map (mo p) cs) (mo p c)
     | Bind(_,_,c,d) => max(mo p c,mo (p+1) d)
     | Tuple(T,l)    => fold max (map (mo p) l) (mo p T)
     | Proj(_,c)     => mo p c
     | LabVT()       => 
     | Case(v,bs)    => 
     | Var(_,c)      => mo p c
     | _             => 0
in  mo 0
end;
************************)

(* test (shallow) dependency of a term on a reference *)
fun depends bref = 
    let fun deprec (Ref(br))       = sameRef br bref
          | deprec (App((c,cs),_)) = (deprec c) orelse (exists deprec cs)
          | deprec (Bind(_,_,c,d)) = (deprec d) orelse (deprec c)
          | deprec (Tuple(T,l))    = (deprec T) orelse (exists deprec l) 
          | deprec (CnLst l)       = exists deprec l
          | deprec (Proj(_,c))     = deprec c
          | deprec (RedTyp(_,c))   = deprec c
          | deprec (LabVT(_,v,t))  = deprec v orelse deprec t
          | deprec (Case(v,bs))    = deprec v orelse deprec bs
          | deprec (Var(_,c))      = deprec c
          | deprec _               = false
     in deprec end;

(* similar but DIFFERENT: does a term mention a name *)
fun mentions nam = 
    let fun mtnrec (Ref(br))       = ref_nam br = nam
          | mtnrec (App((c,cs),_)) = (mtnrec c) orelse (exists mtnrec cs)
          | mtnrec (Bind(_,_,c,d)) = (mtnrec d) orelse (mtnrec c)
          | mtnrec (Tuple(T,l))    = (mtnrec T) orelse (exists mtnrec l)
          | mtnrec (CnLst l)       = exists mtnrec l
          | mtnrec (Proj(_,c))     = mtnrec c
          | mtnrec (RedTyp(_,c))   = mtnrec c
          | mtnrec (LabVT(_,v,t))  = mtnrec v orelse mtnrec t
          | mtnrec (Case(v,bs))    = mtnrec v orelse mtnrec bs
          | mtnrec (Var(_,c))      = mtnrec c
          | mtnrec _               = false
     in mtnrec end;


(* construction of compound bodies... *)
     (* non-binders have one form *)
fun mkAppBod f (b,vs) =
  case share2 (f,map_share f) b
    of UMod => UMod
     | Mod(b') => Mod(b',vs)
fun mkTupleBod f Tls = share2 (f,map_share f) Tls
val mkCnLstBod = map_share
fun mkProjBod f (s,b) =
  case f b
    of UMod => UMod
     | Mod(b') => Mod(s,b')
fun mkRedTypBod f (s,b) =
  case f b
    of UMod => UMod
     | Mod(b') => Mod(s,b')
fun mkLabVTBod f (n,v,t) =
  case share2 (f,f) (v,t)
    of UMod => UMod
     | Mod(v',t') => Mod(n,v',t')
fun mkCaseBod f (v,t) =
  case share2 (f,f) (v,t)
    of UMod => UMod
     | Mod(v',t') => Mod(v',t')

     (* binders have two forms *)
fun mkBindBod f k (t,s,b1,b2) =
  case share2 (f k,f (succ k)) (b1,b2)
    of UMod => UMod
     | Mod(b1',b2') => Mod(t,s,b1',b2')
fun mkBindBod2 f (t,s,b1,b2) = 
  case share2 (f,f) (b1,b2)
    of UMod => UMod
     | Mod(b1',b2') => Mod(t,s,b1',b2')
;


(* canonical term constructors *)
fun mkVar f (u,c) = case f c of UMod => UMod | (Mod c') => Mod(Var(u,c'))
fun umkVar f (u,c) = Var(u,f c)
fun MkApp ((c,[]),_)                  = c
  | MkApp ((App((c',cs'),vs'),cs),vs) = MkApp ((c',cs'@cs),(vs'@vs))
  | MkApp x                           = App(x)
fun mkApp f b =
  let val fb = mkAppBod f b
  in  case fb of UMod => UMod | (Mod fb') => Mod(MkApp(fb'))
  end
fun umkApp f ((c,cs),vs) = MkApp ((f c, map f cs),vs)
fun MkTuple(T,l) =
  let fun standard cs =  (* unfold all rightmost Tuples *)
        case rev cs
	  of (tpl as Tuple(_,ks))::cs => (rev cs)@(standard ks)
	   | cs                       => rev cs
  in  case standard l
	of []  => bug"MkTuple"
	 | [l] => l
	 | ls  => Tuple(T,ls)
  end
fun mkTuple f b = case mkTupleBod f b
		    of UMod => UMod | (Mod b') => Mod(MkTuple b')
fun umkTuple f (c,cs) = MkTuple(f c, map f cs)

fun MkCnLst l = CnLst l
fun mkCnLst f b = case mkCnLstBod f b of UMod => UMod | (Mod b') => Mod(MkCnLst b')
fun umkCnLst f ls = MkCnLst (map f ls)

fun MkProj b = Proj(b)
fun mkProj f b = case mkProjBod f b
		   of UMod => UMod | (Mod b') => Mod(MkProj b')
fun umkProj f (p,c) = MkProj(p,f c);

fun MkRedTyp b = RedTyp(b)
fun mkRedTyp f b = case mkRedTypBod f b
		     of UMod => UMod | (Mod b') => Mod(MkRedTyp b')
fun umkRedTyp f (p,c) = MkRedTyp(p,f c);

fun MkLabVT b = LabVT b
fun mkLabVT f b = case mkLabVTBod f b
		    of UMod => UMod | (Mod b') => Mod(MkLabVT b')
fun umkLabVT f (n,v,t) = MkLabVT(n,f v,f t)

fun MkCase b = Case b
fun mkCase f b = case mkCaseBod f b
		   of UMod => UMod | (Mod b') => Mod(MkCase b')
fun umkCase f (v,t) = MkCase(f v,f t)

(* lifting to avoid capture *)
exception Lift
(** WARNING: This function doesn't use the canonical constructors below **)
fun lift_unshared n =
  if n=0 then (fn _ => UMod)
  else
    let fun lft_rec k (Rel m)  = if m<k then UMod
				  else if (m+n)>0 then  Mod(Rel(m+n))
				       else raise Lift
	  | lft_rec k (App b)   = mkApp (lft_rec k) b
	  | lft_rec k (Bind b)  = mkBind lft_rec k b
	  | lft_rec k (Tuple b) = mkTuple (lft_rec k) b
	  | lft_rec k (CnLst b) = mkCnLst (lft_rec k) b
	  | lft_rec k (Proj b)  = mkProj (lft_rec k) b
	  | lft_rec k (RedTyp b)= mkRedTyp (lft_rec k) b
	  | lft_rec k (LabVT b) = mkLabVT (lft_rec k) b
	  | lft_rec k (Case b)  = mkCase (lft_rec k) b
	  | lft_rec k _         = UMod
    in lft_rec 1
    end
and lift n = share (lift_unshared n)

and MkBind (d as ((Let,_),_,_,b)) = if var_occur b then Bind(d)
				    else lift (~1) b
  | MkBind b                      = Bind(b)
and mkBind f k b =
  let val fb = mkBindBod f k b
  in  case fb of UMod => UMod | (Mod b') => Mod(MkBind b')
  end
and mkBind2 f b =
  let val fb = mkBindBod2 f b
  in  case fb of UMod => UMod | (Mod b') => Mod(MkBind b')
  end
;

fun umkBind f k (t,s,b1,b2) = MkBind((t,s,f k b1,f (succ k) b2))
fun umkBind2 f (t,s,b1,b2) = MkBind((t,s,f b1,f b2));
