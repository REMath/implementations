
signature PRETTY = 
    sig
	type block
	val block         : int * block list -> block
	val string        : string -> block
	val input_line    : instream -> string
	val break         : int -> block
	val annotate      : int list -> block
	val linebreak     : block
	val print         : outstream -> block -> unit
        val indent        : int ref
        val SetLineLength : int -> unit
	val active        : bool ref (* do we want pretty printing? *)
    end;
