(* utils.ml *)

(* failure, bug, and warning *)
exception Failure of string
fun failwith s = raise Failure s
exception Bug of string
fun bug s = raise Bug ("\nbug detected at "^s)


(* New Jersey specials *)

(* Pointer equality !!! *)
fun eq(x:'a,y:'a) = 
      (System.Unsafe.cast(x): 'a ref) = (System.Unsafe.cast(y): 'a ref)

(* Timers *)
local
  open System.Timer
in
  type timer = timer
  type time = time
  val start_timer = start_timer
  val check_timer = check_timer
  val sub_time = sub_time
  val mks_time = fn t => (" "^makestring t)
  val earlier = earlier
  fun makestring_timer t =
    let
      val non_gc_time = check_timer t
      val gc_time = check_timer_gc t
      val sys_time = check_timer_sys t
    in
      "time= "^(makestring non_gc_time)^
      "  gc= "^(makestring gc_time)^
      "  sys= "^(makestring sys_time)
    end
end

fun fst(x,_) = x 
fun snd(_,y) = y
fun thrd(_,_,z) = z

fun do_list f [] = ()
  | do_list f (h::t) = (f h; do_list f t)

fun succ n = n + 1

fun max (x,y):int = if x > y then x else y

fun I x = x

fun length [] = 0 | length (_::t) = 1 + length t

exception Hd
fun hd [] = raise Hd | hd (h::_) = h
exception Tl
fun tl [] = raise Tl | tl (_::t) = t

exception Nth of int
fun nth [] n = raise Nth n
  | nth (h::t) n = if n = 1 then h else nth t (n-1)

fun string_of_num (n:int) = makestring n

exception Assoc
fun ASSOC e [] = raise Assoc
  | ASSOC e (h::t) = if fst h = e then h else ASSOC e t
fun assoc e l = snd (ASSOC e l)

fun exists f [] = false
  | exists f (h::t) = (f h) orelse (exists f t)

fun for_all f [] = true
  | for_all f (h::t) = (f h) andalso (for_all f t)

fun equal_fst u (x,y) = (u=x) 

val mem_assoc = exists o equal_fst

fun neg f e = not (f e)

fun sep_last [] = failwith "sep_last"
  | sep_last (h::t) = 
    let val pair = (h,t) 
        fun sep_last_aux (pair as (h,[])) = pair
          | sep_last_aux (h,h'::t') = 
            let val pair = (h',t')
                val (x,l) = sep_last_aux pair in (x,h::l) end
     in sep_last_aux pair end

fun except_last [] = failwith "except_last"
  | except_last (h::t) = 
    let val pair = (h,t) 
        fun except_last_aux (_,[]) = []
          | except_last_aux (x,h'::t') = 
              let val pair = (h',t') in x :: (except_last_aux pair) end
     in except_last_aux pair end

fun chop_list n l =
    let fun chop_aux 0 (l1,l2) = (rev l1, l2)
          | chop_aux n (_,[]) = failwith "chop_aux"
          | chop_aux n (l1,(h::t)) = chop_aux (n-1) (h::l1, t)
     in chop_aux n ([],l) end


fun first_n 0 l = []
  | first_n n [] = failwith "first_n"
  | first_n n (h::t) = h::(first_n (n-1) t)


fun repeat n action arg =
    let fun repeat_action n =
            if n <= 0 then () else (action arg; repeat_action (n-1))
     in repeat_action n end

fun interval n m =
    let fun interval_n (l,m) =
            if n > m then l else interval_n (m::l, m-1)
     in interval_n ([],m) end

fun C f x y = f y x


(* printing *)
fun prts out s = output(out,s)
fun prti out i = output(out,makestring(i:int))
fun prtnl out = output(out,"\n")
fun prtmsg out s = let open Pretty
		   in  print out (block (0,[string s,linebreak]))
		   end
val prs = prts std_out
val pri = prti std_out
fun line() = prtnl std_out
val message = prtmsg std_out;


(* structure sharing *)
datatype 'a modif = Mod of 'a | UMod;

fun share f x =
  case (f x) of (Mod y) => y | UMod => x;
fun share2 (f1,f2) (xy as (x,y)) =
  case (f1 x,f2 y)
    of (Mod x',Mod y') => Mod(x',y')
     | (Mod x', Umod) => Mod(x',y)
     | (Umod, Mod y') => Mod(x,y')
     | (UMod,UMod) => UMod
fun map_share f =  
    let fun map_share_f (x::l) =
            (case (f x)
	       of (Mod x') => Mod(x'::share_map_share_f l)
	        | Umod => (case map_share_f l
			     of (Mod l') => Mod (x::l')
			      | UMod => UMod))
	  | map_share_f [] = UMod
        and share_map_share_f l = share map_share_f l
    in map_share_f end;



(* list operators *)
exception Empty of string

fun last []  = raise Empty "last"
  | last [x] = x
  | last (x::xs) = last xs
fun dropLast []  = raise Empty "dropLast"
  | dropLast [x] = []
  | dropLast (x::xs) = x :: dropLast xs
fun removeLast l = (last l, dropLast l)
      handle Empty _ => raise Empty "removeLast"
	
fun foldr f a (x::xs) = f x (foldr f a xs)
  | foldr f a []      = a
fun foldl f a (x::xs) = foldl f (f a x) xs
  | foldl f a []      = a
fun foldr1 f [] = raise Empty "foldr1"
  | foldr1 f l  = let val (last,front) = removeLast l
		  in  foldr f last front
		  end

fun member x = exists (fn z => z=x)
val mem = member


(*******************  not in use **********************
fun dedup (x::xs) = if member x xs then dedup xs else x::(dedup xs)
fun setDiff (x::xs) ys = if member x ys then setDiff xs ys
			 else x::(setDiff xs ys)
  | setDiff [] _ = []
fun do_list_funny f g [x] = f x
  | do_list_funny f g (h::t) = (f h;g();do_list_funny f g t)
  | do_list_funny f g [] = bug"do_list_funny"
********************************************************)

(* do not change order of list *)
fun filter_pos p = 
    let fun select x res = if p x then x::res else res
    in foldr select [] end
fun filter_neg p = 
    let fun select x res = if p x then res else x::res
    in foldr select [] end
fun split p =
    let fun select x (res_pos,res_neg) =
      if p x then (x::res_pos,res_neg) else (res_pos,x::res_neg)
    in foldr select ([],[]) end
fun until p =
  fn [] => ([],[])
   | ys as (x::xs) =>
      if not(p x)
	then let val (f,b) = until p xs in  (x::f,b) end
      else ([],ys)


(* lists of strings *)
fun concat_sep sep =
  let fun cs (s::[]) = s
	| cs (s::ss) = s^sep^(cs ss)
	| cs [] = ""
  in cs
  end

(* a functional utility *)
fun Repeat n fnc arg = if (n<=0) then arg 
                       else fnc (Repeat (n-1) fnc arg);

(* apply to a pair *)
fun pair_apply f (x,y) = (f x,f y);
