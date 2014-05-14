(* $Id: build.sml,v 1.18 1998/11/10 15:23:24 ctm Exp $ *)

val version = "LEGO 1.3.1 (Solaris)";
val qwertyuiop = System.Timer.start_timer();

(* To get cml support without the -cml command switch, set the CMLLIB 
   environment variable - for LFCS it's /usr/local/share/njml/cml.
   Under Linux you also need the SRCDIR variable, since getWD doesn't work.

   This is all a horrible hack to deal with various possible cml configs
*)

val cmldir =  
let fun check [] = "none"
  | check (h::t) =  if (substring(h,0,7) = "CMLLIB=" handle Substring => false)
                    then substring(h,7,size h - 7) else check t
in check (System.environ())
end

val srcdir =  
let fun check [] = System.Directory.getWD ()
  | check (h::t) =  if (substring(h,0,7) = "SRCDIR=" handle Substring => false)
                    then substring(h,7,size h - 7) else check t
in check (System.environ())
end;

if cmldir = "none" then () else (System.Directory.cd cmldir;use "load-cml");
if cmldir = "none" then () else (loadCML(); System.Directory.cd srcdir);

val NJMLLIB =
  let 
  fun check [] = "/usr/local/share/njml/smlnj-lib"
    | check (h::t) =
      if (substring(h,0,8) = "NJMLLIB=" handle Substring => false)
      then substring(h,8,size h - 8) else check t
  in check (System.environ())
  end
;

print ("Using New Jersey Library from "^NJMLLIB^"\n");

val NJMLLIB=NJMLLIB^"/";



(* it would be better to use the SourceGroup module *)
use (NJMLLIB^"lib-base-sig.sml");
use (NJMLLIB^"lib-base.sml");
use (NJMLLIB^"pathname-sig.sml");
use (NJMLLIB^"pathname.sml");
use (NJMLLIB^"charset-sig.sml");
use (NJMLLIB^"charset.sml");
use (NJMLLIB^"ctype-sig.sml");
use (NJMLLIB^"ctype.sml");
use (NJMLLIB^"string-util-sig.sml");
use (NJMLLIB^"string-util.sml");
use (NJMLLIB^"list-util-sig.sml");
use (NJMLLIB^"list-util.sml");
use (NJMLLIB^"list-format-sig.sml");
use (NJMLLIB^"list-format.sml");
use (NJMLLIB^"makestring-sig.sml");
use (NJMLLIB^"makestring.sml");

use "PRETTY.sml";
use "Pretty.sml";
use "utils.sml";
use "universe.sml";
use "term.sml";
use "error-sig.sml";
use "type-sig.sml";
use "infix.sml";
use "shar_pretty.sml";
use "subst.sml";
use "esUMopen.sml";
use "toc.sml";
use "type.sml";
use "unif.sml";
use "cml.sml";
use "namespace-sig.sml";
use "machine-sig.sml";
use "machine.sml";
use "concrete-sig.sml";
use "concrete.sml"; 
use "qmaster-sig.sml";
use "qmaster.sml";
use "conor-sig.sml";
use "conor-ind.sml";
use "ind_relations-sig.sml";
use "ind_relations.sml";
use "relation-sig.sml";
use "nind_rel.sml";
use "double-sig.sml";
use "newextra_ind.sml";
use "theorems-sig.sml";
use "more_ind.sml";
use "record-sig.sml";
use "record.sml";
use "synt-sig.sml";
use "synt.sml";
use "conor-knots.sml";
use "conor-then.sml";
use "tacticals-sig.sml";
use "tacticals.sml";
use "toplevel-sig.sml";
use "toplevel.sml";
use "discharge-sig.sml";
use "discharge.sml";
use "namespace.sml";
use "newtop-sig.sml";
use "newtop.sml";
use "tactics-sig.sml";
use "tactics.sml";
use "conor-top.sml";
use "logic.sml";
use "help.sml";
use "modules-sig.sml";
use "modules.sml";
use "init-sig.sml";
use "init.sml";
use "error.sml";
use "pbp.sml";
use "linkOpen.sml";
use "interface.sml";

(* debugging help *)
fun show nam =
  case (Namespace.search nam (Namespace.getNamespace()))
    of Bd{bd=(_,_,c,_),...} => c;
Init.Init_raw "XCC";
Pbp.pbp_initialize();

use "genCore.sml";

(* Ideally, support for Proof-by-Pointing is added dynamically
   by the User Interface *)
use "pbp_lib_logic.sml";
use "pbp_lib_eq_basics.sml";

use "lib_nat_plus_thms.sml";

message("\ncompile: "^(makestring_timer qwertyuiop));

make_lego true version;
(***
Profile.reset();
***)
