(*<TITLE>conor-sig.sml</TITLE>
<H2>conor-sig.sml</H2>

<XMP>
*)

signature VOODOO =
sig
  type voolabel (* = string * int *)
  datatype voodoo =
    Voo of voolabel               (* herein lies the voodoo *)
  | VProp
  | VTheory                                  (* the type of theories *)
  | VType of node
  | VRef of binding
  | VRel of int                                         (* variable *)
  | VApp of (voodoo * (voodoo list)) * (prntVisSort list) (* application *)
  | VBind of bindVisSort * string * voodoo * voodoo
  | VVar of int * voodoo                      (* existential variable *)
  | VTuple of voodoo * (voodoo list)           (* elem of Sig *)
  | VProj of projSort * voodoo
  | VLabVT of label * voodoo * voodoo          (* labeled trm:typ pair *)
  | VCnLst of voodoo list                     (* for use in Theories *)
  | VRedTyp of instrs * voodoo   (* reduce the synthesised type using insts *)
  | VCase of voodoo * voodoo        (* case *)
  | VBot
  type voobind (* = voolabel * bindVisSort * string * voodoo *)
  type vooctxt (* = voobind list *)
  type voostate (* = vooctxt * voodoo *)
  exception too_much_voodoo
  exception missing_voodoo
  exception voodoo_no_rewrite
  val voofold : 'a -> (voolabel -> 'a) -> ('a -> 'a -> 'a) -> voodoo -> 'a
  val voomap : (voolabel -> voodoo) -> voodoo -> voodoo
  val start : cnstr -> voostate
  val introvoo : string -> int -> voostate -> voostate
  val voo : cnstr -> voodoo
  val stop : voostate -> cnstr
  val vootype : voodoo -> voodoo
  val voorewrite : (voodoo->voodoo)->voodoo->voodoo
  val voolift : (voodoo->voodoo)->voostate->voostate
  val sub : voolabel -> voodoo -> voostate -> voostate
  val shove : voobind -> voolabel -> voostate -> voostate
  val fetch : voolabel -> voostate -> voobind
  val swap : voobind -> voostate -> voostate
  val elide : voolabel -> voostate -> voostate
  val dep1l : voodoo -> voolabel list
  val dep1g : vooctxt -> voolabel -> voolabel list
  val deple : vooctxt -> voolabel -> voolabel list
  val vooprint : voodoo -> unit
  val vooprintstate : voostate -> unit
end

signature CONORINDUCTIVENEEDS =
sig
  exception bad_elim
  structure Concrete : CONCRETE
  val normal : cnstr -> cnstr
  val define : (string list * cnstr) list -> unit
  val elim_rule : string -> (cnstr * cnstr)
  val con_list : string -> (string * cnstr) list
  val eq_info : unit -> {name : cnstr,
                         refl : cnstr,
                         sym : cnstr,
                         subst : cnstr}
  val app_synth : cnstr -> cnstr -> cnstr
  val conflict_stuff : unit -> {truth:cnstr,
                                falsity:cnstr,
                                plan:cnstr}
end;

signature CONORINDUCTIVE =
sig
  val DoConorTheorems : string -> unit
  val DoConorInversion : string -> unit
end;

signature CONORTOPNEEDS =
sig
    exception not_inductive
    val get_inductive_info : cnstr -> {instance       : cnstr,
				   name           : string,
				   type_of_name   : cnstr,
				   param_types    : cnstr list,
				   param_vis      : visSort list,
				   constructors   : string list,
				   con_types      : cnstr list,
				   inst_params    : cnstr list,
				   inst_vis       : prntVisSort list,
				   ind_params     : cnstr list,
				   ind_vis        : prntVisSort list,
				   elim_rule      : cnstr,
				   elim_rule_type : cnstr,
				   elim_inst      : cnstr,
				   elim_inst_type : cnstr}
    exception cannot_do_intros
    val intros_t : int -> (cnstr * cnstr)
    val refine_t : int -> cnstr -> unit
    val replace_t : int -> (cnstr * cnstr) -> unit
    val conf_qrepl : (string*string*string) -> unit
    val addConfig : string*string*string*string->unit
    val findConfig : string -> (string*string*string) ->
	(string*string*string)
    val isNewName : string -> bool
    val getGoal : int -> cnstr
    val checking_stuff : bool->{on:bool,name:cnstr,kill:cnstr,
                                look:cnstr->cnstr}
    val tactic_wrapper : (unit -> unit) -> unit -> unit
    structure ConorInductiveNeeds : CONORINDUCTIVENEEDS
    structure Namespace : NAMESPACE
end;

signature CONORTOP =
sig
  type cnstr_c
  type qtac
  val QTacList : (qtac list) ref
  val Induction : cnstr_c -> int -> unit
               (* ind term or pos *)
  val Invert : int -> cnstr_c -> unit
            (* goal,  term *)
  val Qnify : bool -> int  -> cnstr_c -> unit
           (* whnf?, #eqs,   equality to use or Prop_c *)
  val ConfigEquality : (string*string*string) -> unit
                  (* Eq,  Eq_refl, Eq_subst *)
  val ConfigQnify : (string*string*string) -> unit
                  (* nat,  thm, unused *)
  val ConfigTheorems : (string*string*string) -> unit
                  (* true, false, true_not_false *)
end;

(*
</XMP>
*)
