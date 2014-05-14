signature TACTICALS =
    sig
	val tactical_else : (unit -> unit) -> (unit -> unit) -> unit -> unit
	val tactical_fail : unit -> unit
	val tactical_succeed : unit -> unit
	val tactical_try : (unit -> unit) -> unit -> unit
	val tactical_repeat : (unit -> unit) -> unit -> unit
	val tactical_for : int -> (unit -> unit) -> unit -> unit
    end;
