signature MODULES =
    sig
	type LoadKind

        exception DepCheckDone of string list
	val LK_STRING : LoadKind
	val LK_INTERACTIVE : LoadKind
        val SetSaveObjects: bool -> unit
	val Load : string -> unit
	val Make : bool -> string -> unit
	val MakeUnsafe  : string -> unit
	val ReloadFrom  : string -> string -> unit
	val Include : string -> unit
	val ModuleImport
	    : (string * time) * LoadKind * bool ->
                (string * string list) -> unit
        val DepCheck
	    : (string * time) * LoadKind * bool ->
                (string * string list) -> unit
	val legoFileParser
	    : ((string * time) * LoadKind * bool -> (unit -> unit) -> unit) ref
	val legoStringParser : (string -> unit) ref

    end;
