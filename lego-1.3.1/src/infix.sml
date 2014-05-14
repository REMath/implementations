signature INFIX = 
  sig
    exception InfixInternal

    datatype Associativity = LAssoc | RAssoc | NAssoc

    (* Actually non-associative operators aren't available, so
       NAssoc is used for all manner of ghastly hacks
    *)
    val infix_sym: string -> string    (* op{whatever} -> {whatever} *)
    val infix_name: string -> string   (* the inverse *)

    val strAssoc: Associativity -> string;
    val strPri: int -> string;

    val infix_data: string -> (Associativity * int);
    val nameIsInfix: string -> bool;

    val infix_register: string -> Associativity -> int -> bool
    val infix_forget: string -> unit;
   
    val init_infix: unit -> unit;
end       
 
structure Infix: INFIX =
struct
  exception InfixInternal
  
  datatype Associativity = LAssoc | RAssoc | NAssoc;

  val infix_list = ref ([]: (string * Associativity * int) list);

  fun init_infix () = 
     infix_list:=[]


(* Used to default to

   [ ("/\\",LAssoc, 3), ("\\/",LAssoc,2) ]; *)

  fun strPri x = nth ["1","2","3","4","5","6","7","8","9"] x;

  val strAssoc = fn 
     LAssoc => "left"
   | RAssoc => "right"
   | NAssoc => raise InfixInternal;

  fun infix_name "\\/" = "or"
   |  infix_name "/\\" = "and"
   |  infix_name x = "op"^x;

  fun infix_sym "or" = "\\/"
   |  infix_sym "and" = "/\\"
   |  infix_sym s =
    (case explode s of  "o"::"p"::r => (implode r)
            | _ => raise InfixInternal);

  fun infix_data s = 
    let fun search nil = (NAssoc,~1)
         |  search ((r as (n,a,i))::l) = if s = n then (a,i) else search l
    in search (!infix_list)
    end;

  fun nameIsInfix s = 
    let fun search s nil = false
         |  search s ((r as (a,_,_))::l) = if s = a then true else search s l
    in (search (infix_sym s) (!infix_list)) handle InfixInternal => false
    end;

  fun register s a i =
    (message ("Infix "^s^" "^(strAssoc a)^" "^(strPri i));
    infix_list := (s,a,i)::(!infix_list));

  val defaults_list = [("+",(LAssoc,5)), ("-",(LAssoc,5)), 
                       ("/",(LAssoc,6)), ("*",(LAssoc,6))];

  fun infix_register s NAssoc _ =

     let fun getprec [] c = (NAssoc,~1)
         |   getprec ((c',i)::r) c = if c=c' then i else getprec r c

     in (case getprec defaults_list (hd (explode s)) of
         (_,~1) => (message "No default precedence available"; false)
        | (a,i) => (register s a i;true))
     end
   | infix_register s a i =
     if (i>9) orelse (i<1) then (message "Precedence out of range"; false)
     else (register s a i; true)
  
  fun infix_forget n =
     let fun sr [] = raise InfixInternal
	   | sr ((n',a,i)::r) = if n = n' then r else ((n',a,i)::(sr r))
     in infix_list:= sr (!infix_list)
     end;

end

