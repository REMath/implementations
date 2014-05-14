signature MACHINE =
  sig
    val ConsiderVar : int -> cnstr -> cnstr * cnstr
    val Projection : projSort -> cnstr * cnstr -> cnstr * cnstr
    val tuplize 
      : (int * cnstr) list
      -> cnstr -> (cnstr * cnstr) list 
      -> (cnstr * cnstr) * (int * cnstr) list
    val Apply 
      : (int * cnstr) list
      -> (cnstr -> cnstr)
      -> prntVisSort
      -> cnstr * cnstr
      -> cnstr * cnstr -> (cnstr * cnstr) * (int * cnstr) list
    val ConsiderType  : string -> cnstr * cnstr
    val ConsiderTypen : int -> cnstr * cnstr
    val ConsiderProp : unit -> cnstr * cnstr
    val ConsiderTheory : unit -> cnstr * cnstr
    val letize : cnstr * cnstr -> binding -> cnstr * cnstr
    val abstract : cnstr * cnstr -> binding -> cnstr * cnstr
    val generalize : cnstr * cnstr -> binding -> cnstr * cnstr
    val sigize : cnstr * cnstr -> binding -> cnstr * cnstr
  end;
  
