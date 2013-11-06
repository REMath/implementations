signature TOPLEVEL =
    sig
	type cnstr_c
	val nullTac : substitution -> unit
	val AutoTac : (substitution -> unit) ref
	val init_toplevel : unit -> unit
	val Pr : unit->unit
	val PR : unit -> unit
	val AppTac : ('a -> 'b) -> 'a -> unit
	val smallAppTac : ('a -> 'b) -> 'a -> unit
	val RefineTac_c 
	    : int -> int -> cnstr_c -> (assignment list -> unit) -> unit
	val SolveTacn : int -> int -> cnstr_c -> bool
	val KillRef : unit -> unit
	val IntrosTac : int -> string list -> bool -> int
	val Goal : cnstr_c -> string * LocGlob -> unit
	val UNDO : int -> unit
	val Refine : int -> int -> cnstr_c -> unit
	val Claim : cnstr_c -> unit
	val Next : int -> unit
	val Intros : int -> bool -> string list -> unit
	val Save_frz_default : freeze ref
    end;
