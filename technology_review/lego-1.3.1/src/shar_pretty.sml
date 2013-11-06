(* pretty.sml    un programme d'impression             *)
(* Author         : Randy Pollack                      *)
(* Modified by    : Dilip Sequeira, Randy Pollack & Thomas Kleymann  *)

(* 17 Nov 1996 Thomas Schreiber

               This module could do with some serious
               reimplementation. Should anyone have the engergy to do
               so, I recommend that in pretty-printing mode, the block
               format is converted to annotations so that e.g., an
               Emacs interface can insert linebreaks and indentation
               where appropriate. *)


local
(* interactive_mode is used to tell if in interactive mode or not.
 * it is pushed whenever a file is opened, and popped when a
 * file is closed *)
    val interactive_mode = ref ([]:bool list)

(* Annotations
   -----------
   are sent out by the pretty printer to effeciently communicate with
   a user-interface such as the generic Emacs interface for theorem
   provers developed by Goguen, Kleymann, Sequeira and others.
   See the LFCS Technical Report ECS-LFCS-97-368 for details.

   At the user level, 

     Configure AnnotateOn;

   tells the PrettyPrinter to output annotations. After

     Configure AnnotateOff;

   annotations are no longer printed. This is the default.

   Annotations should never be included in the object file.
   To temporarily suspend annotations, we use the variable
   AnnotatingNow. 

   AnnotatingNow is modified by exit_file, go_to_file, Interactive,
   SetAnnotating. It is queried by isAnnotating.

 *)
    val AnnotatingNow = ref false;	(* really output annotations *)
    val Annotating = ref false;		(* in AnnotateOn mode *)
in
    fun interactive () = (!interactive_mode)=[];
    fun Interactive () = (interactive_mode := [];
			  AnnotatingNow:= (!Annotating))

    fun SuspendAnnotations () = AnnotatingNow := false;
    fun ResumeAnnotations () = if interactive()
				   then AnnotatingNow := (!Annotating)
			       else ()


    fun go_to_file () = (SuspendAnnotations();	                 
			 interactive_mode := true::(!interactive_mode))
    fun exit_file () = (interactive_mode := tl (!interactive_mode);
			ResumeAnnotations())
	

    fun SetAnnotating isActive =
      (Annotating := isActive;
       AnnotatingNow := isActive;
       message ("Annotating is now "^
		(if isActive then "enabled" else "disabled")))

    fun isAnnotating () = !Annotating andalso !AnnotatingNow
    fun hasAnnotations () = !Annotating
end;

datatype dfnsPrnt = OmitDfns | ElideDfns | ShowDfns | Marks 

signature PRETTY =
  sig
    val SetPrettyPrinting: bool -> unit
    val isPrettyPrinting : unit -> bool
    val indent : int ref
    val SetLineWidth : int -> unit
    val message : string -> unit
    val loudmessage: string -> unit
    val prnt : cnstr -> unit
    val input_line : instream -> string
    val print_words : string list -> unit
    val legoprint : cnstr -> unit
    val print_expand : cnstr -> unit
    val prl : (int * cnstr) list -> unit
    val prnt_vt : cnstr -> cnstr -> unit
    val prnt_vt_expand : cnstr -> cnstr -> unit
    val os_prnt_exp : outstream -> cnstr -> unit
    val os_prnt_red : outstream -> cnstr -> unit
    val prnt_red : cnstr -> unit
    val prnt_defn : string -> cnstr -> cnstr -> unit
    val prnt_decl : visSort -> string -> cnstr -> unit
    val print_cannot_assume      : string -> cnstr -> cnstr -> unit
    val print_value : string -> cnstr -> unit
    val print_type  : string -> cnstr -> unit
    val print_refine : int -> cnstr -> unit
    val print_qrepl  : cnstr -> cnstr -> cnstr -> unit
    val print_ctxt   : dfnsPrnt -> binding -> unit
  end  

(* The choice of names are mainly for historic reasons and should be   *)
(* adapted one day.

   _exp means that terms will be printed in extended form *)

(* The expanded version is aimed towards the creation of object  *)
(* files. As Tim Heap has pointed out to me, these should not be *)
(* pretty-printed                                                *)

signature LEGOFORMAT = 
    sig
	type block
  datatype prCnstr =
    PrProp
    | PrType  of node
    | PrRef   of string
    | PrRel   of int
    | PrApp   of prCnstr * ((prCnstr * prntVisSort) list)
    | PrBind  of string list * bindVisSort * prCnstr * prCnstr
    | PrVar   of int * prCnstr
    | PrTuple of prCnstr * (prCnstr list)
    | PrProj  of projSort * prCnstr
    | PrRedTyp of instrs * prCnstr
    | PrThry
    | Pr_theory of (string * prCnstr * prCnstr) list
    | PrCast of (string list * bindVisSort * prCnstr) list * prCnstr * prCnstr
          (* rewrite  reductions  *)
    | PrRedBod of (prCnstr * prCnstr) list  (* rewriting reductions *)
    | PrBot


	datatype granularity = explicit | implicit 
	  | tuples			(* explicit, but non-dependent
					 tuples will have no typing
					 information *) 
	val whnfr : (cnstr -> cnstr) ref
	val SetPrettyPrinting: bool -> unit
	val isPrettyPrinting : unit -> bool
	val SetLineWidth     : int -> unit
	val indent        : int ref
	val newline       : block
	val postlf        : block -> block
	val block         : (int*block list) -> block
	val break         : int -> block
	val annotate      : int list -> block
	val string        : string -> block
	val myblock       : block list -> block
	val format_words : string list -> block list
	val format           : granularity -> cnstr -> block
	val legoformat       : cnstr -> block
	val format_expand    : cnstr -> block
	val format_goal      : (int*cnstr) -> block
	val format_vt        : cnstr -> cnstr -> block
	val format_vt_expand : cnstr -> cnstr -> block
	val format_red       : cnstr -> block
	val format_decl      : visSort -> string -> cnstr -> block
	val format_cannot_assume      : string -> cnstr -> cnstr -> block
        val format_value     : string -> cnstr -> block
	val format_type      : string -> cnstr -> block
	val format_refine    : int -> cnstr -> block
	val format_ctxt      : dfnsPrnt -> binding -> block
	val print            : outstream -> block -> unit
	val ffp : granularity -> bool -> cnstr -> prCnstr
    end;

functor FunErrorFormatting (structure LegoFormat:LEGOFORMAT) : ERRORFORMATTING
    =
    struct
	type cnstr = cnstr
	type format = LegoFormat.block
		
	fun print bl = LegoFormat.print std_out (LegoFormat.postlf bl)
	fun block n bl = LegoFormat.block (n,bl)
	val newline = LegoFormat.newline

	fun cnstr_format true  = LegoFormat.format LegoFormat.explicit
	  | cnstr_format false = LegoFormat.format LegoFormat.implicit

	val formatWord = LegoFormat.string

	fun formatString s
	    = LegoFormat.block (0,
			    LegoFormat.format_words
			    (StringUtil.tokenizep CType.isSpaceOrd (s,0)))
    end

(* We use the qwertz toolbox' Pretty module to format the output. The  *)
(* algorithm is based on Paulson, ML for the Working Programmer,       *)
(* section 8.9. Notice that if linelength=0, this effectively turns    *)
(* pretty printing off                                                 *)

(* Instead of sending everything to the outstream, we send it to a     *)
(* pretty-print stream.                                                *)

(* format_words sl seperates the words in sl by a space                *)
(* format pretty_print_mode exp_flg formats a lego expression. If      *)
(* exp-flg then the expression will be expanded                        *)
(* legoformat = format false followed by a linefeed                    *)
(* format_expand = format explicit followed by a linefeed              *)
(* format_goal will format an unexpanded current goal                  *)
(* format_vt v t will format a value and a type, seperated by a colon  *)
(* format_vt_expand will do the same but expand, both value and type   *)
(* format_red will format a reduction (without expanding)              *)
(* format_decl will format a declaration                               *)
(* format_cannot_assume id v t will print an error message if v is of 
                               type t and t is not a kind              *)
(* format_value uses legoformat to format a value                      *)
(* format_type  uses legoformat fo format a type                       *)
(* format_refine g v uses legormat to format the value v which has 
                     has refined goal g                                *)
(* format_ctxt b will print the defintion of b in the context          *)
(* print prints a formatted block                                      *)
 

functor FunPretty (structure LegoFormat : LEGOFORMAT) : PRETTY =
struct

  local
      open LegoFormat

    val prnso = print std_out
    fun AvoidPrettyPrinting f x =
      let val active = isPrettyPrinting()
      in  (if active then SetPrettyPrinting false else ();
	   f x;
	   SetPrettyPrinting active)
      end
  in
    val isPrettyPrinting = isPrettyPrinting
    val SetLineWidth = SetLineWidth
    val message = prnso o postlf o string
    fun loudmessage str = 
       if hasAnnotations () then prnso (postlf (string ("\254"^str^"\255")))
	   else message str
    val indent = indent
    val prnt = prnso o (format implicit)
    val input_line = Pretty.input_line
    val print_words = prnso o postlf o myblock o format_words

    fun SetPrettyPrinting isActive =
      (LegoFormat.SetPrettyPrinting isActive;
       print_words ["Pretty","printing","is","now",
		    if isActive then "enabled" else "disabled"])


    val legoprint = prnso o legoformat 
    val print_expand = AvoidPrettyPrinting (prnso o format_expand)
    val prl  = do_list  (prnso o format_goal) 
    fun prnt_vt v = prnso o  (format_vt v)
    fun prnt_vt_expand v = AvoidPrettyPrinting (prnso o (format_vt_expand v))
    fun os_prnt_exp os  = AvoidPrettyPrinting ((print os) o (format tuples))
    fun os_prnt_red os  = AvoidPrettyPrinting ((print os) o format_red)
    val prnt_red = prnso o format_red

    fun prnt_defn id v t =
      if interactive()
	then (prnso (block (2, [string "defn", break 2] @
			    (format_words [id,"="]) @
			    [break 1, legoformat v]));
	      prnso (block (2, (break 6) ::
			    (format_words [id,":"]) @
			    [break 1, legoformat t])))
      else prnso (block (8, (format_words ["defn ",id,"=","...",":"]) @
			 [break 1,legoformat t]))
			     
    fun prnt_decl v id = prnso o (format_decl v id)
    fun print_cannot_assume id v = prnso o postlf o (format_cannot_assume id v)
    fun print_value id = prnso o postlf o (format_value id)
    fun print_type id = prnso o postlf o (format_type id)
    fun print_refine g = prnso o (format_refine g)

    fun print_qrepl v lhs rhs =
      (prnso (block (2, [string "Qrepl", break 2, legoformat v]));
       prnso (block (2, [format implicit lhs, break 1, string "=>",
			 break 1, legoformat rhs])))

    fun print_ctxt f = prnso o (format_ctxt f)
  end
end;

functor FunLegoFormat (structure Infix: INFIX) : LEGOFORMAT = 
struct

    datatype granularity = explicit | implicit 
  | tuples			(* explicit, but non-dependent
				 tuples will have no typing
				 information *) 

  val whnfr = ref (I : cnstr -> cnstr)     (* set to whnf function *)
  local
    open Pretty
  in 
    type block = Pretty.block
    val block = Pretty.block
    val annotate = annotate
    fun SetPrettyPrinting isActive
      = Pretty.active:=isActive
		   
    fun isPrettyPrinting _ = (!active)
    fun myblock bl = block (0, bl)
    val string = string
    val add_myint = string o (makestring:int->string)
    val newline = linebreak
    fun postlf bl = block (0,[bl,newline])
    val break = break
    val print = print
    val emptyblock = string ""
    val SetLineWidth = SetLineLength
    val indent = indent 
    val _ = SetPrettyPrinting true (****************************)
    val _ = (indent := 0)
  end

  local
      fun t2s2 b [] = "!)"
        | t2s2 b (h::t) = (if b then "(!" else " ")^h^(t2s2 false t)
  in  fun tag2string [] = "(! !)"
        | tag2string x = t2s2 true x
  end

  fun bb l r m = myblock [string l, m, string r]  
  val square = bb "[" "]"
  val parens = bb "(" ")"
  val curly = bb "{" "}"
  val pointed = bb "<" ">"
  val expBr = bb "<*" "*>"  (* show expansion *);

  fun relates R l r = [l, string R, r]
  val colon = relates ":"
  val gencolon = relates " : " (* generous colon *)

  (* format existential variables n |-> ?n *)
  fun format_mvar n = myblock [string "?", add_myint n]

  (* A concrete syntax for pretty-printing *)
  datatype prCnstr =
    PrProp
    | PrType  of node
    | PrRef   of string
    | PrRel   of int
    | PrApp   of prCnstr * ((prCnstr * prntVisSort) list)
    | PrBind  of string list * bindVisSort * prCnstr * prCnstr
    | PrVar   of int * prCnstr
    | PrTuple of prCnstr * (prCnstr list)
    | PrProj  of projSort * prCnstr
    | PrRedTyp of instrs * prCnstr
    | PrThry
    | Pr_theory of (string * prCnstr * prCnstr) list
    | PrCast of (string list * bindVisSort * prCnstr) list * prCnstr * prCnstr
          (* rewrite  reductions  *)
    | PrRedBod of (prCnstr * prCnstr) list  (* rewriting reductions *)
    | PrBot;

  val bindSym =
    fn Vis => ":" | Hid => "|" | Def => "=" | VBot => bug"bindSym"
  val builtinInfixSym =
    fn Pi => "->" | Sig => "#"    (* | Lda => "\\" *)
     | _ => ""                       (** "" means no infix; force var  **)
  val projSym = fn Fst => ".1" | Snd => ".2" | Labl(s) => "^"^s

  (* format for printing *)
  fun ffp granularity isRed = 
    let
      val exp_flg = not (granularity=implicit)
      fun ffpef c =
	case c of
	  Var(n,c) => PrVar(n,(if exp_flg then ffpef c else PrBot))
	| Prop     => PrProp
	| Theory   => PrThry
	| Type(i)  => PrType(i)
	| Ref(br)  => PrRef (case ref_kind br
                        of (GenTag tag) => tag2string tag
                         | _ => ref_nam br)
	| Rel(n)   => PrRel(n)
	| App((c,gs),vs) => 
	  let
	    val vs =
	      if exp_flg then map (fn NoShow => ShowExp | v => v) vs
	      else if for_all (fn v => v=NoShow) vs
		     then map (fn NoShow => ShowForce | v => v) vs
		   else vs
	    fun ap (c,NoShow) gvs = gvs
	      | ap (c,pv) gvs     = (ffpef c,pv)::gvs
	  in  PrApp(ffpef c,foldr ap [] (ListUtil.zip (gs,vs)))
	  end
	| Bind((Thry,_),_,_,CnLst bs) =>
	  let fun aux (LabVT(Name s,v,t)) = (s,ffpef v,ffpef t)
		| aux _ = bug"ffpef:theory"
	  in  Pr_theory (map aux bs)
	  end
	| Bind(bv,s,c,d) => ffp_binder bv s c d
	| Tuple(T,ls)    => ffp_tuple T ls
	| Proj(p,c)      => PrProj(p,ffpef c)
	| LabVT(_,v,t)   => PrCast([],ffpef v,ffpef t)   (** temp **)
	| RedTyp(i,c)    => PrRedTyp(i,ffpef c)
	| CnLst cs       => if isRed then ffp_red cs
			    else bug"ffpef;CnLst"
	| Bot            => PrBot
      and ffp_binder (bv as (bind,_)) s c1 c2 =
	let
	  val showVar = (exp_flg andalso s<>"") orelse var_occur c2
	  val _ = if showVar andalso s="" then bug"ffp_binder"
		  else ()
	  val forceVar = (not showVar) andalso (builtinInfixSym bind = "")
	  val s = if forceVar then "_" else s
	in
	  case (showVar orelse forceVar,ffpef c2)
	    of (false,x) => PrBind([],bv,ffpef c1,x)
	     | (true,(inr as PrBind((ls as (_::_)),bv',c,x))) =>
		 if bv=bv' andalso c=ffpef (lift (length ls) c1)
		   then PrBind(s::ls,bv,c,x)
		 else PrBind([s],bv,ffpef c1,inr)
	     | (true,x) => PrBind([s],bv,ffpef c1,x)
	end
      and ffp_tuple T ls =
	let
	  fun isDepTpl (T,[_]) = false
	    | isDepTpl (T,_::ls) =
	      (case (!whnfr) T
		 of Bind((Sig,_),_,_,tr) =>
		      var_occur tr orelse isDepTpl (tr,ls)
		  | _ => bug"isDepTpl1" )
	    | isDepTpl _ = bug"isDepTpl2"
	  val T = if (granularity=explicit) orelse isDepTpl(T,ls)
		    then ffpef T
		  else PrBot
	  in  PrTuple(T,map ffpef ls)
	end
     and ffp_red ls =
       let fun mkPrRedBod [] = []
	     | mkPrRedBod (LabVT(RedPr,c1,c2)::cs) =
	         (ffpef c1,ffpef c2)::(mkPrRedBod cs)
	     | mkPrRedBod _ = bug"ffp_red"
       in  PrRedBod (mkPrRedBod ls)
       end
    (***************************
and ffp_sharCast (V,T) =
     let 
       fun pre_sC (PrV,PrT) =
	 case (PrV,PrT)
	       of (PrBind(ns,bv as (b,v),pc,pd),
		 PrBind(ns',(b',v'),pc',pd')) =>
		 if ((b=Let andalso b'=Let) orelse (b=Lda andalso b'=Pi))
		   andalso ns=ns' andalso v=v' andalso pc=pc'
                     then case pre_sC (pd,pd')
			    of PrCast(front,pl,pr) =>
			         PrCast((ns,bv,pc)::front,pl,pr)
			     | _ => bug"pre_sC"
                     else PrCast([],PrV,PrT)
	         | _ => PrCast([],PrV,PrT)
	  in pre_sC (ffpef V,ffpef T)
	  end
**************************)
    in ffpef
    end;


(* put a numeric extension on a print-name if the current binder is in the
 * scope of another binder with the same print-name, or there is a reference
 * to global with the same print name in the scope of the current binder
 *)
  fun add_name s nams prc =
    let
      fun pro (PrRef(nam'))     = s = nam'
	| pro PrProp            = false
	| pro PrThry            = false
	| pro (Pr_theory _)     = false   (****************)
	| pro (PrType(_))       = false
	| pro (PrVar(_,t))      = pro t
	| pro (PrRel(_))        = false
	| pro (PrApp(c,l))      = (pro c) orelse (exists (pro o fst) l)
	| pro (PrBind(_,_,c,d)) = (pro c) orelse (pro d)
	| pro (PrTuple(T,ls))   = (pro T) orelse (exists pro ls)
	| pro (PrProj(_,c))     = pro c
	| pro (PrRedTyp(_,c))   = pro c
	| pro (PrCast(ls,c,T))  = (pro c) orelse (pro T)  (******)
	| pro (PrRedBod(ccs))   = exists (fn (c,d) => pro c orelse pro d) ccs
	| pro PrBot             = false
    in
      if (s="") orelse (s="_") orelse (not (mem s nams) andalso not (pro prc))
	then (string s, s::nams)
      else add_name (s^"'"^(makestring ((length nams)+1))) nams prc
    end;

  local open Infix in
  fun format_ granularity isRed nams c =
    let
      val exp_flg = not (granularity=implicit)

      (* format_univ_levl:node -> block *)
      fun format_univ_levl (Uvar(Named(s),_)) = parens (string s)
	| format_univ_levl (Uconst(n)) = parens (add_myint n)
	| format_univ_levl (Uvar(Unnamed(n),_)) = emptyblock

      val bracket =
	fn Pi => curly
	 | Lda => square
	 | Sig => pointed
	 | Let => square
	 | Thry => bug"format_:bracket";

      fun path_wrap l ls = 
	  if isAnnotating () then 
	      (annotate (rev l))::(ls@[annotate [252]])
	  else ls 
      (* This is a bit of a hack: the 250 and 251 codes will be added
         in the prettyprinting module when path-compression happens.
	 Pretty.sml *)

      fun fr_rec path names c = 
	case c
	  of PrRef(nam)  => string nam
	   | PrProp      => (case theory() 
			       of lf => string "Type"
				| _  => string "Prop" )
	   | PrThry => string "Theory"
	   | Pr_theory bs => string("theory["^concat_sep "," (map #1 bs)^"]")
	   | PrType(nod) => 
	       (case theory()
		  of lf => string "Kind"
		   | _  => case nod of
		       (Uvar(Unnamed(n),_)) => string "(Type)"
		     (* parenthesis are needed due to
		      LEGO's ambiguous grammar *)
		     | _ => myblock [string "Type",
				     format_univ_levl nod])
	   | PrVar(n,t) =>
	       if exp_flg then expBr (pr_exp_Var path names n t)
	       else format_mvar n
	   | PrRel(n) =>
	       (string (nth names n)  
		handle Nth _ =>  (** in case of open subterm **)
		  (expBr (myblock [string "Rel ",
				   add_myint n])))
	   | PrApp(b) => parens
                (case b of (PrRef(x),[n1,n2]) => 
                   if nameIsInfix x 
		       then fr_infix path names (NAssoc,"no") x n1 n2
		   else fr_apps path names b
   	         | _ => fr_apps path names b)

	   | PrBind(l,bv,c3,c4) => 
	       parens (myblock (fr_binder path names (bv,c3,c4) l))
	   | PrTuple(b) => parens (pr_tuple path names b)
	   | PrProj(s,c) =>
	       myblock [(case c
			   of PrRef(_)  => fr_rec path names c
			    | PrRel(_)  => fr_rec path names c
			    | PrProj(_) => fr_rec path names c
			    | _         => parens (fr_rec path names c)),
			string (projSym s)]
	   | PrRedTyp(i,c) =>
	       parens (myblock (string"NormTyp "::fr_outer_rec path names c))
	   | PrCast(b) => parens (pr_cast path names b)
	   | PrRedBod(ccs) => fr_red_bod path names ccs
	   | PrBot     => string "_"

      and fr_outer_rec path names c = 
	(* some outermost parens not needed; otherwise fr_outer_rec
	 * does the same as fr_rec
	 *)
	case c of
	  PrBind(l,bv,c3,c4) => fr_binder path names (bv,c3,c4) l
	| PrApp(b) => 
             (case b of (PrRef(x),[n1,n2]) => 
                if nameIsInfix x 
		    then [fr_infix path names (NAssoc,"no") x n1 n2]
		else [fr_apps path names b]
              | _ => [fr_apps path names b])
	| PrType(Uvar(Unnamed _,_)) => [string "Type"]
	| x              => [fr_rec path names x]

      and fr_infix_rec path names ii b =
         (case (b,ii) of 
            (PrApp(app as (PrRef(x),[n1,n2])),_) => 
             if nameIsInfix x then [fr_infix path names ii x n1 n2]
  	                        else [fr_apps path names app]
	  | (PrBind((_::_),_,_,_),(LAssoc,_)) => 
	      (string "(")::(fr_outer_rec path names b)@[string ")"]
 	  |  _ => fr_outer_rec path names b)

      and fr_apps path names (c,args) =
	let fun prarg path =
	  let fun SMtoString ShowNorm = " "
		| SMtoString ShowForce = "|"
		| SMtoString ShowExp = "%%"
		| SMtoString _ = (bug "fr_apps";"")
	  in fn (c,ShowMode) => 
	     	(string (SMtoString ShowMode))::
		((path_wrap path [(fr_rec path names c)])@[break 0])
	  end
	in let fun argloop n p [] = []
		 | argloop n p (a::l) =  (prarg (n::p) a)::((argloop (n+1) p l))
	   in myblock ((path_wrap (1::path) [fr_rec (1::path) names c])@
		       (ListUtil.flatten (argloop 1 (2::path) args)))
	   end
	end
	
      and fr_infix path names (branch, par) nam (a1,_) (a2,_) =
          let val sym = infix_sym nam in 
	      let val arg1 = path_wrap (1::2::path) 
		   	(fr_infix_rec (1::2::path) names (LAssoc, sym) a1)
		  val arg2 = path_wrap (2::2::path) 
		      	(fr_infix_rec (2::2::path) names (RAssoc, sym) a2)
	      in let val txt = 
		  myblock (arg1@
			  ((break 1)::(path_wrap (1::path) [string sym]))@
			  ((break 1)::arg2))
		 in case branch of 
		     NAssoc => if par = "no" then txt else parens txt
		   |  _  => if par = sym
				then if branch = fst (infix_data sym)
					 then txt else parens txt
			    else if snd (infix_data nam) > snd (infix_data par)
				     then txt else parens txt
		 end
	      end
          end
      and fr_binder path names ((b,v),c,d) l =
	let 
	  fun pbr n p (nams:string list) ls =
	    case ls
	      of []   => bug "fr_binder"
               | [l]  => let val (name, scope) = add_name l nams d
                           in (myblock (path_wrap (n::p) [name]),scope)
			 end
	       | (l::ls) =>
		   let val (name,scope) = add_name l nams d
		     val (name',scope') = pbr (n+1) p scope ls
		   in  (myblock ((path_wrap (n::p) [name])
				 @[string ",", name']), scope')
		   end
	in 
	  case l
	    of [] => let val (name,scope) = add_name "" names PrBot
		     in  (path_wrap (1::2::path) [fr_rec (1::2::path) names c])
			@(path_wrap (1::path) [string(builtinInfixSym b)])@
	                 [break 0]@
			  (path_wrap (2::2::path) (fr_infix_rec (2::2::path)
						   scope (NAssoc,"yes") d))
		     end
	     | ls => let val (name,scope) = pbr 1 (1::path) names ls
                         val l1 = (path_wrap (1::path) [name])
	                 val l2 = path_wrap (2::path) 
					(fr_outer_rec (2::path) (tl scope) c)
                         val l3 = path_wrap (3::path)
				   (fr_infix_rec (3::path) scope (NAssoc,"") d)
                         in (bracket b 
	                       (myblock (l1@((string (bindSym v))::l2))))::
	                    ((break 0)::l3)
		     end
	end

      and pr_exp_Var path names n t =
	myblock (colon (format_mvar n) (fr_rec path names t))

      and pr_tuple path names (T,ls) = 
	let
	  fun mapcolon f [] = []
	    | mapcolon f [x] = [f x]
	    | mapcolon f (h::t) = f h::string ","::mapcolon f t
	in
	  myblock ((mapcolon (myblock o (fr_outer_rec path names)) ls) @
		   (if T=PrBot then [] 
		    else (string ":" :: fr_outer_rec path names T)))
	end

      and pr_cast path names (ls,c,T) =  (********************)
	myblock (colon (myblock (fr_outer_rec path names c))
		 (myblock (fr_outer_rec path names T)))
		
      and fr_red_bod path names ccs =
	let 
	  fun prb (c1,c2) = myblock [(myblock (fr_outer_rec path names c1)),
				     break 2,
				     string "==>",
				       break 2,
				       (myblock (fr_outer_rec path names c2))]

	  fun PRB (cc::[]) = [prb cc]
	    | PRB (cc::ccs) = prb cc             ::
	      break 0      ::
	      string "|| " ::
	      PRB ccs
	    | PRB [] = [emptyblock]
	in 
	  myblock (string "   " :: PRB ccs)
	end
	    
    in
      path_wrap [] (fr_outer_rec [] nams (ffp granularity isRed c))
    end
  end (* of local open Infix *)

  val format_words =
    dropLast o ListUtil.flatten o map (fn s => [string s, break 1]) 

  fun format exp_flg c = myblock (format_ exp_flg false [] c)

  val legoformat = postlf o (format implicit)
			
  val format_expand_ = format_ explicit false []

  val format_expand = postlf o myblock o format_expand_

  fun format_goal (n,c)
    = postlf (block (2, [if isAnnotating() then string "  \253" 
			                   else string "   ",
			 myblock (gencolon (format_mvar n) 
				  (myblock (format_ implicit false [] c)))]))
	

  fun format_vt v t = myblock (gencolon (myblock (format_ implicit false [] v))
			       (legoformat t))

  fun format_vt_expand v t = 
    postlf (myblock (gencolon (myblock (format_expand_ v))
		     (myblock (format_expand_ t))))

  val format_red = postlf o square o myblock o (format_ implicit true [])

  fun format_decl v id t =
    block (8, (format_words ["decl ", id, if v=Vis then ":" else "|"]) @
	   [break 1, legoformat t])


  fun format_cannot_assume id v t =
    block (2, [string "cannot assume", break 1,
	       string id, break 1,
	       string ":", break 1] @
	   (format_expand_ v) @
	   [break 1,
	    string ":", break 1,
	    format_expand t])

  fun format_value "" v = block (2, (format_words ["value", "="]) @
				 [break 1, format implicit v])
    | format_value id v = block (2, (format_words ["value", "of", id, "="]) @
				 [break 1, format implicit v])

  fun format_type "" v = block (2, (format_words ["type ", "="]) @
				[break 1, format implicit v])
    | format_type id v = block (2, (format_words ["type ", "of", id, "="]) @
				[break 1, format implicit v])
  fun format_refine g v =
    block (2, [string "Refine", break 1] @
	   (if g>0 then [add_myint g, break 1] else []) @
	      [string "by", break 2,
	       legoformat v])

  fun format_ctxt _ (Bd {kind=Mrk (module,imports,_,_), ...})
    = postlf (block (5, format_words (" ** Module" :: module ::
				      (case imports of
					 [] => []
				       | _  => "Imports" :: imports))))
    | format_ctxt Marks _                                = emptyblock
    | format_ctxt _ (Bd {kind=Red, bd = (_,_,v,_), ...}) = postlf (format_red v)
    | format_ctxt _ (Bd {kind=Config (a,b,c,d), ...})
      = postlf (block (4, format_words [" ** Config",a,b,c,d]))
    | format_ctxt _ (Bd {kind=LabelTag (tag,name), ...})
      = postlf (block (4, format_words [" ** Label",tag2string tag,name]))
    | format_ctxt OmitDfns (Bd {bd=((Let,_),_,_,_), ...}) = emptyblock
    | format_ctxt elideFlg (Bd {bd=((Let,_),id,v,t), frz=frz, param=param, 
                                kind = K, ...})
      = postlf (block (4, [if (!frz)=Froz then string "*" else break 1,
			     if param=Local then string "$" else break 1,
                               case K
                                 of GenTag tag =>
                                    string (" Gen "^(tag2string tag)^" as ")
                                  | _ => break 0,
			       if isAnnotating() then string "\253" 
			                         else break 0,
			       string id, break 1,
			       string "=", break 1,
			       if elideFlg=ElideDfns then (string "...")
			       else (format implicit v),
				 break 1, string ":", break 1,
				 format implicit t]))
    | format_ctxt _ (Bd {bd=((_,vis),id,v,_), param=param, ...})
      = postlf (block (4, [break 1,
			   if param=Global then string "$"
			   else break 1, 
			       if isAnnotating () then string "\253" 
			                          else break 0,
			     string id, break 1, 
			     string (if vis=Hid then "|" else ":"),
			     break 1, format implicit v]))
end; (* of structure LegoFormat *)		   


structure LegoFormat = FunLegoFormat (structure Infix = Infix);
structure Pretty = FunPretty (structure LegoFormat = LegoFormat);
open Pretty;

