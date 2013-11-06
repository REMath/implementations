(* $Log: build-linux.sml,v $
 * Revision 1.3  1998/11/10 15:23:13  ctm
 * Modified to have 1.3.1 release message
 *
 * Revision 1.2  1998/10/30 14:07:49  ctm
 * quartermaster added
 *
 * Revision 1.1  1998/07/07 16:18:29  tms
 * This build file works under bellart provided
 *
 *   1) You use New Jersey SML with support for the library e.g.,
 *         /home/tms/njml/Linux-bin/sml-njlib
 *
 *   2) Set SRCDIR to the directory of the SML sources
 *
 *   3) Set CMLLIB to the directory of the CML sources e.g.,
 *         /home/tms/njml/cml
 *
 * And yes. It would be better to only have a single build.sml file.
 * Merge build.sml and build-linux.sml if you know how!!!
 *
 * Revision 1.13  1997/08/26 09:05:03  tms
 * Build module for bellart@dcs.ed.ac.uk
 *
 * Revision 1.12  1997/05/08 13:42:12  tms
 * added support for adding tactics
 *
 * Revision 1.11  1997/03/06 17:35:58  djs
 * Added some stuff to build.sml so we could configure cml-ness from th
 * environment.
 *
 * Revision 1.10  1997/03/06 15:59:16  tms
 * added basic support for Point-and-Rewrite
 *
 * Revision 1.9  1997/03/06 09:51:24  tms
 * *** empty log message ***
 * *)

val version = "LEGO 1.3.1 (Linux)";
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
