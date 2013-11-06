(* $Id: modules.sml,v 1.12 1998/11/10 15:29:13 ctm Exp $ *)
functor FunModules (structure Top:TOP and
			Toplevel:TOPLEVEL and
			Namespace:NAMESPACE and
			Synt:SYNT
			) (* : MODULES *) =
    struct
(* filename utility *)
fun splitPath path =
  let
    val split_ext =
      fn "l"::"."::rest => (rest,"l")
       | "o"::"."::rest => (rest,"o")
       | x => (x,"")
    fun to_frst_slash so_far =
      fn [] => (so_far,[""])
       | (rest as ("/"::t)) => (so_far,rest)
       | h::t => let val (nam,rest) = (to_frst_slash so_far t)
		 in  (h::nam,rest)
		 end
    val (rest,ext) = split_ext (rev (explode path))
    val (nam,path) = to_frst_slash [] rest
  in
    (implode (rev path),implode (rev nam),ext)
  end;

(* searching for files *)
local
  structure Dir = System.Directory
  structure SIO = System.Unsafe.SysIO
  structure CI = System.Unsafe.CInterface
  fun find_file name =
      let
	  fun concat a b = implode ((explode a) @ (explode b))
      fun ff snam =   (* for following symbolic links *)
	let val path = SIO.PATH snam
	in
	  case SIO.ftype path handle CI.SystemCall s => SIO.F_DIR
	    of SIO.F_DIR => NONE
	     | SIO.F_REGULAR =>
		 SOME (name,SIO.mtime path,SIO.access(snam,[SIO.A_READ]))
	     | SIO.F_SYMLINK =>
		   ff (let val readlink = SIO.readlink snam
		       in
			   if Pathname.isAbsolutePath readlink then readlink
			   else concat (Pathname.dirOfPath snam)
			               readlink
		       end)
	     | _ => NONE
	end
    in ff name
    end
  fun find_file_using_path name =
    if (ord name = ord"/") orelse (ord name = ord"~")
      then fn _ => find_file name
    else fn [] => NONE
          | h::t => (case find_file (h^name)
		       of NONE => find_file_using_path name t
			| x => x)
  fun find_file_using_legopath name =
    let
      fun ffp [] = NONE
	| ffp (h::t) = (case find_file (h^name)
			  of NONE => ffp t
			   | x => x)
    in
      if (ord name = ord"/") orelse (ord name = ord"~")
	then find_file name
      else ffp (Top.legopath())
    end
  fun check_file_ok nam =
    fn SOME(filnam,tim,true) => (filnam,tim)
     | SOME(filnam,_,false) =>
	 failwith("Searching for file "^nam^";\nfound "^filnam^
		  ",\nbut you can't read it.")
     | NONE =>
	 failwith("Searching for file "^nam^";\nno appropriate file found.")
in
  fun find_file_dotl nam =
    case splitPath nam
      of (_,_,"") => check_file_ok nam (find_file_using_legopath (nam^".l"))
       | (_,_,"l") => check_file_ok nam (find_file_using_legopath nam)
       | (_,_,"o") => check_file_ok nam (find_file_using_legopath nam)
       | _ => bug"find_file_dotl"
  fun find_file_dotl_doto nam =
    case splitPath nam
      of (_,_,"l") => check_file_ok nam (find_file_using_legopath nam)
       | (_,_,"o") => check_file_ok nam (find_file_using_legopath nam)
       | (_,_,"") => 
	     let
	       val doto = find_file_using_legopath (nam^".o")
	       val dotl = find_file_using_legopath (nam^".l")
	       val newer =
		 case (doto,dotl)
		   of (NONE,SOME(_)) => dotl
		    | (SOME(_),NONE) => doto
		    | (SOME(_,otim,_),SOME(_,ltim,_)) =>
			if earlier (otim,ltim) then dotl
			else doto
		    | _ => NONE
	     in check_file_ok nam newer
	     end
       | _ => bug"find_file_dotl_doto"
end;

(* output "compiled" state *)

(**************************
(* improve sharing on term-type pairs *)
fun sharing VT =
  case VT
    of (Bind((btv as (Lda,vsl)),nml,M1,M2),Bind((Pi,vsr),nmr,N1,N2)) =>
          if vsl=vsr andalso nml=nmr andalso sameterm (M1,N1)
	    then let val (cx,vt) = sharing (M2,N2)
		 in  ((btv,nml,M1)::cx,vt)
		 end
	  else ([],VT)
     | (Bind((btv as (Let,_)),nml,M1,M2),Bind((Let,_),nmr,N1,N2)) =>
          if nml=nmr andalso sameterm (M1,N1)
	    then let val (cx,vt) = sharing (M2,N2)
		 in  ((btv,nml,M1)::cx,vt)
		 end
	  else ([],VT)
     | _ => ([],VT);
***************)

fun writeCompiled filenam modnam =
  let
      val _ = SuspendAnnotations ();
    val (hit,new,old) = Namespace.splitCtxt (fn br => sameMrk br modnam)
      ("Mark \""^modnam^"\" not found; "^modnam^".o not written")
      (Namespace.getNamespace())
    val new = hit::new
    fun compile os br =
      let
	fun pr_deps br =
	  let val deps = ref_deps br
	  in  if deps = [] then ()
	      else prts os ("//"^(concat_sep " " deps))
	  end
  	fun lgDefn br =
	  let val (v,t) = ref_vt br
	  in  prts os ((if !(ref_frz br)=Froz then"*"
			else if ref_param br=Local then "$" else "")^
		       "["^ref_nam br^" : ");
	      os_prnt_exp os t;
	      prts os "\n  = "; os_prnt_exp os v;
	      pr_deps br; prts os "];\n"
	  end
	fun lgDecl br =
	  (prts os ((if ref_param br=Global then "$" else "")^"["^ref_nam br^
		    (if ref_vis br = Hid then " | " else " : "));
	   os_prnt_exp os (ref_typ br); pr_deps br; prts os "];\n")
        local
            fun t2s2 b [] = "!)"
              | t2s2 b (h::t) = (if b then "(!" else " ")^h^(t2s2 false t)
        in  fun tag2string [] = "(! !)"
              | tag2string x = t2s2 true x
        end
      in
	if Namespace.activeProofState()
	  then failwith("Hit eof of module \""^modnam^
			"\"\n  while still in proof state;\""^
			filenam^"\" not written")
	else
	  case (ref_kind br,ref_isDefn br)
	    of (Bnd,true) => lgDefn br
	     | (Bnd,false) => lgDecl br
             | (GenTag tag,true) =>
                 ((prts os ("Generate "^(tag2string tag)^" "));(lgDefn br))
             | (GenTag _,false) =>
                 failwith("Cannot write Generated declaration")
	     | (Red,_) => (os_prnt_red os (ref_red br); prts os ";\n")
	     | (Mrk(s,i,_,_),_) =>
		 prts os ("Module "^s^
			  (if i=[] then ""
			   else " Import \""^(concat_sep "\" \"" i)^"\"")^";\n")
	     | (Config(a,x,y,z),_) =>
		 prts os ("Configure "^a^" "^x^" "^y^" "^z^";\n")
             | (LabelTag(tag,name),_) =>
                 prts os ("Label "^(tag2string tag)^" "^name^";")
	     | (StThry nam,_) => failwith("Cannot write .o while Theory \""^
					  nam^"\" is unclosed")
      end
    val os = open_out filenam
    val _ = map (compile os) new
    val _ = close_out os
    val _ = ResumeAnnotations ()
  in
    message ("Wrote "^filenam)
  end handle Io s => message("Warning: "^s^"\n"^filenam^" not written");

(* Switch for saving objects back, or not *)

val objectSave = ref true;

fun SetSaveObjects x = objectSave:=x;

(** commands to support Luca's 'mock modules' **)

fun findMrk mrk =
  let fun fm (br::brs) =  if sameMrk br mrk then SOME(br) else fm brs
	| fm [] = NONE
  in fm (Namespace.getNamespace())
  end
fun definedMrk mrk = not (findMrk mrk = NONE);

(* the time field of mit is the time the file was opened;
 * Namespace.addMark also stores the time the mark is made *)

fun Mark (mrk,imports,name,time) =
  if Namespace.activeProofState() then failwith"no marking in proof state"
  else if (not (definedMrk mrk))
	   then (loudmessage("Creating mark \""^mrk^"\" ["^name^"]");
		 Namespace.addMark (mrk,imports,time))
       else failwith("mark \""^mrk^"\" already in namespace");

datatype LoadKind =
    LK_MAKE of string
  | LK_MAKEUNSAFE of string
  | LK_LOAD of string
  | LK_INCLUDE of string
  | LK_DEPCHECK of string list
  | LK_STRING
  | LK_INTERACTIVE;

(* "foward referencing" so the actions of the grammar can
 * parse files (e.g. 'Include') and strings (e.g. 'Logic')
 *)
val legoFileParser = ref (fn ((filnam:string,
			       filtim:time),
			      lk:LoadKind,
                              exec:bool) =>
			  fn (closAct:unit->unit) => ())
val legoStringParser = ref (fn (str_nam:string) => ());

(* Exception for aborting parser after modules declaration *)

exception DepCheckDone of string list;

local
  fun includ nt clos = (Namespace.killRef(); (!legoFileParser) nt clos)
  fun mk_ld filnam ff lk =
    let
      val (_,nam,_) = splitPath filnam
    in
      if definedMrk nam
	then message("module \""^nam^"\" already loaded: no action")
      else let
	     val (nt as (fullpath,_)) = ff filnam
	     val (path,_,ext) = splitPath fullpath
	     fun closing() =
                 (let val mark = findMrk nam
	          in (case findMrk nam
	            of SOME(br) => message("(** time since mark \""^nam^"\": "^
		 	  		    makestring_timer (ref_marktim br)^
					    " **)")
  		     | NONE => message("Warning: expected mark \""^nam
			 		^"\" not found");
		      if ext="l" then (writeCompiled (path^nam^".o") nam)
		      else ())
		  end)
	   in includ (nt,lk nam,false)
                (if !objectSave then closing 
                   else (fn() => message (".o file not written.")))
	   end
    end

in
  fun ForgetOld fnam =
  let val (_,nam',_) = splitPath fnam
      in  case (findMrk nam') of 
	       NONE => ()
	     | SOME(br) => 
		   let val (_,modtime) = find_file_dotl fnam 
		   in  if earlier(ref_filtim br,modtime) then 
			   Namespace.ForgetMrk nam'
		       else ()
		   end
      end

  fun DepCheck (_,LK_DEPCHECK(done_list),true) (nam,imports) =
      let fun loop done [] = raise (DepCheckDone done)
	    | loop done (module::rest) = 
	      if mem module done 
		  then loop done rest
	      else 
		(includ (find_file_dotl module, LK_DEPCHECK done, true)
		   (fn()=>())
		 handle DepCheckDone(newdone) => loop newdone rest)
      in loop (nam::done_list) imports
      end
    | DepCheck _ _ = bug "DepCheck: Unexpected Arguments"

  fun Include nam = includ (find_file_dotl nam,LK_INCLUDE nam,false) (fn()=>())
  fun Load filnam = mk_ld filnam find_file_dotl LK_LOAD
  fun Make initial filnam =
    (if initial then 
       (message ("Checking Dependencies for "^filnam); 
        ForgetOld filnam;  (* Just in case file not on lego path *)
	includ (find_file_dotl filnam, LK_DEPCHECK [filnam], true) (fn()=>())
        handle DepCheckDone _ => 
           message ("Dependencies Checked"))
     else ();  
     mk_ld filnam find_file_dotl_doto LK_MAKE)
  fun MakeUnsafe filnam = mk_ld filnam find_file_dotl_doto LK_MAKEUNSAFE
  fun ReloadFrom loadFilnam forgetFilnam =
    let
      val (_,forgetNam,_) = splitPath forgetFilnam
    in
      (if definedMrk forgetNam then Namespace.ForgetMrk forgetNam else ();
       Load loadFilnam)
    end

  fun ModuleImport ((filenam,filetim),ldknd,xec) (nam,imports) =
    let
      val (_,Nam,_) = splitPath filenam
      val _ = if definedMrk nam
		then failwith("Trying to Include module \""^nam^
			 "\" which already exists.  Use Make, Load or Reload")
	      else message ("Including module "^nam)
      val _ = if (nam<>Nam) andalso (not (interactive()))
		then message("Warning: module name \""^nam
			     ^"\" does not equal filename \""^filenam^"\"!")
	      else ()
    in
      (case ldknd
	 of LK_INCLUDE lnam =>
		      (message("Warning: Including file "^lnam^
			       " which contains Module "^nam^
			       "; Imports propagated as Include");
		       do_list Include imports)
	  | LK_LOAD _ => do_list Load imports
	  | LK_MAKE _ => do_list (Make false) imports
          | LK_DEPCHECK _ => bug "ModuleImport: DepCheck"
	  | LK_INTERACTIVE =>               
	       (do_list (Make false) imports)
	  | LK_STRING =>
	       (message("Warning: Use of Module command in string.");
			do_list (Make false) imports)
	  | _ => bug"ModuleImport";
       Mark (nam,imports,filenam,filetim))
    end

end
end

