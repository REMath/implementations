(* universe.ml *)
(* Author: Randy Pollack <pollack@cs.chalmers.se> *)

(* CHANGES 

   Thomas Schreiber <tms@lfcs.ed.ac.uk>

   1994
   removed the function print_univ_levl, 
   pretty printing is now handled by the module Pretty 

   February 1995
   added ImpredicativeSums, predicativeSums
   to incorporate small impredicative \Sigma-types 
*)

(* "mode" operations are placed here because they must be first *)

val TypeType = ref false
and LuosMode = ref true
and PredicativeSums = ref true;

fun ImpredicativeSums() = (PredicativeSums:=false; 
                           message"small impredicative Sigma-types")
and Predicativesums() = (PredicativeSums:=true; 
                         message"strong predicative Sigma-types")
and TypeInType() = (TypeType:= true; message"Type in Type")
and TypesStratified() = (TypeType:= false; message"Types Stratified");

datatype theories = lf | pureCC | xtndCC;

local val inference = ref(xtndCC,false) 
in fun set_inference (t,e) = (inference := (t,e))
   and theory _ = fst (!inference)
   and eta _ = snd (!inference)
end;

val LF = (lf,true)
and LF_no_n = (lf,false)
and PCC = (pureCC,false)
and PCC_n = (pureCC,true)
and XCC = (xtndCC,false)
and XCC_n = (xtndCC,true);

(********************************************
This is not a satisfactory implementation.  The graph is stored as a list,
with new info added to the fromt of the list.  Thus the state of the graph
may be rolled back when unification backtracks.
*******************************************)

datatype node_lim = Num of int | Infinity
datatype label = Unnamed of int | Named of string
type node_body = int * node_lim * (label list) * (label list)
         (*      min ,   max ,       gt_list ,     ge_list  *)
type labeled_node_body = label * node_body
datatype node = Uvar of labeled_node_body | Uconst of int
datatype univ_cnstrnt = UniGe of node | UniGt of node
type univ_graph = labeled_node_body list;

(****** for debugging ***********)
local
  val prNL = fn Num(n) => pri n | Infinity => prs"^"
  val prLab = fn (Unnamed n) => (pri n;prs",") | (Named s) => prs(s^",")
  fun prLst lst = (prs" ["; map prLab lst; prs"]")
in
  val prNode =
    fn Uconst(n) => (prs"T";pri n)
     | Uvar(Unnamed n,(min,max,gt,ge)) => 
	 (prs"V";pri n;prs"  ";pri min;prs"-";prNL max;prLst gt;prLst ge)
     | Uvar(Named s,(min,max,gt,ge)) => 
	 (prs"V";prs s;prs"  ";pri min;prs"-";prNL max;prLst gt;prLst ge)
end;
(*********************************)

fun nodLim_gt m (Num(n)) = m > n 
  | nodLim_gt m Infinity = false;


val NBR_UVARS = ref 0
val UVARS = ref ([]:univ_graph)
fun Init_universes() = (UVARS:= []; NBR_UVARS:= 0; ());


fun fnd_nod (Uvar(i,_)) nods = (Uvar(ASSOC i nods) handle _ => bug"fnd_nod")
  | fnd_nod (nod as Uconst(_)) nods = nod;

fun node_equal (Uvar(k,_)) (Uvar(l,_)) = k=l
  | node_equal (Uconst(m)) (Uconst(n)) = m=n
  | node_equal _ _                     = false;


exception Universes of string;


fun add_cnstrnts (i,csts) =
  let
  fun propagate (Mnan as (M,n,an)) ii =
    (if M > !NBR_UVARS then raise Universes "cycle" else ();
     let val (imin,imax,gt,ge) = ((assoc ii an)
				  handle _ => bug"propagate:assoc")
     in if imin >= n then Mnan              (* i already >= j*)
	else if nodLim_gt n imax 
	       then raise Universes "constant limits headroom"
	     else let val an = (ii,(n,imax,gt,ge))::an     
                                       (* make i >= j, and propagate *)
		  in foldl propagate 
		    (M+1,n,thrd(foldl propagate (M+1,n+1,an) gt)) ge 
		  end 
     end)
  fun add_cnstr an (UniGe j) =
    if node_equal i j then an 
    else
      (case (fnd_nod j an,i)
	 of (Uvar(jj,(jmin,jmax,gt,ge)),Uvar(ii,_))
	    => if (mem ii ge) orelse (mem ii gt) then an
	       else thrd(propagate 
			 (0,jmin,(jj,(jmin,jmax,gt,ii::ge))::an) ii)
	  | (Uconst n,Uconst m)
	    => if m >= n then an else raise Universes "constants clash"
	  | (Uvar(jj,(jmin,jmax,gs1,gs2)),Uconst m)
	    => (case (jmin <= m, nodLim_gt (m+1) jmax)
		  of (true,false) => (jj,(jmin,Num(m),gs1,gs2))::an
		   | (true,true)  => an
		   | (false,_)    => raise Universes 
		                                 "constant limits headroom") 
	  | (Uconst n,Uvar(ii,_)) => thrd(propagate (0,n,an) ii) )
    | add_cnstr an (UniGt j) =
      (case (fnd_nod j an,i)
	 of (Uvar(jj,(jmin,jmax,gt,ge)),Uvar(ii,_))
	    => if mem ii gt then an
	       else thrd(propagate
			 (0,(jmin+1),(jj,(jmin,jmax,ii::gt,ge))::an) ii)
	  | (Uconst n,Uconst m)
	    => if m > n then an else raise Universes "constants clash"
	  | (Uvar(jj,(jmin,jmax,gs1,gs2)),Uconst m)
	    => (case (jmin < m, nodLim_gt m jmax)
		  of (true,false) => (jj,(jmin,Num(m-1),gs1,gs2))::an
		   | (true,true)  => an
		   | (false,_)    => raise Universes 
                                             "constant limits headroom" ) 
	  | (Uconst n,Uvar(ii,_)) => thrd(propagate (0,(n+1),an) ii))
  in
    if !TypeType then () else UVARS:= foldl add_cnstr (!UVARS) csts
  end;

local
  fun ac_batch l =
    let val an = !UVARS
    in 
      (do_list add_cnstrnts l; true) handle Universes s => (UVARS:= an; false)
    end
in
  fun univ_equal i j =
    (node_equal i j) orelse ac_batch [(i,[UniGe j]),(j,[UniGe i])]
  fun univ_leq i j = ac_batch [(j,[UniGe i])]
end;

fun uvar nam l = 
  let
    fun act() = 
      let
	val init_bod = (0,Infinity,[],[]);
	val dum_lab_bod = (Named"",init_bod)
	val lab = (NBR_UVARS:= (!NBR_UVARS+1);
		   if nam="" then Unnamed(!NBR_UVARS)
		   else Named(nam))
	val (is_old,old) = (true,ASSOC lab (!UVARS))
		            handle Assoc => (false,dum_lab_bod)
	val lab_bod =  if is_old then old else (lab,init_bod)
	val nod = Uvar(lab_bod)
      in  
	(if is_old then () else UVARS:= (lab_bod::(!UVARS));
	 add_cnstrnts(nod,l);
	 nod)
      end
  in case l
       of [UniGt(Uconst n)]                 => Uconst(succ n)
        | [UniGe i]                         => i
        | [UniGe(Uconst i),UniGe(Uconst j)] => Uconst(max(i,j))
        | _                                 => act()
  end
local   
  val Uconst0 = Uconst 0
  val Uconst1 = Uconst 1
  val Uconst2 = Uconst 2
in
  fun uconst 0 = Uconst0     (* optimize storage *)
    | uconst 1 = Uconst1
    | uconst 2 = Uconst2
    | uconst j = Uconst j
end;


fun clean_graph() =
    let fun cgr new (nod as (n,_)) = if mem_assoc n new then new else nod::new
        val uvars = !UVARS
    in  (UVARS:= [];   (* allow release of memory *)
         prs"clean graph: before= "; pri (length uvars);
         prs", after= "; 
         pri (length (UVARS:= rev (foldl cgr [] uvars); !UVARS));
         line() ) end;

