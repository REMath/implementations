(* arraystack.ml *)
(* stack of pointers implemented as an array *)


(* grow an array *)
let growArray (arr: 'a array) (newLen: int) (null: 'a) : 'a array =
begin
  let newArr : 'a array = (Array.make newLen null) in

  (* copy *)
  (Array.blit
    arr                   (* source array *)
    0                     (* source start position *)
    newArr                (* dest array *)
    0                     (* dest start position *)
    (Array.length arr)    (* number of elements to copy *)
  );

  (* return new array *)
  newArr
end


(* ensure the array has at least the given index, growing its size
 * if necessary (by doubling) *)
let ensureIndexDoubler (arr: 'a array ref) (idx: int) (null: 'a) : unit =
begin
  while ((Array.length !arr) < (idx+1)) do
    arr := (growArray !arr ((Array.length !arr) * 2) null);
  done;
end


(* the stack must be given a dummy value for unused array slots *)
class ['a] tArrayStack (null: 'a) =
object (self)
  (* ---- data ---- *)
  (* number of (non-null) elements in the array *)
  val mutable len: int = 0;

  (* the array; its length may be greater than 'poolLength', to
   * accomodate adding more elements without resizing the array *)
  val mutable arr: 'a array = (Array.make 16 null);

  (* ---- funcs ---- *)
  method length() : int = len

  method isEmpty() : bool = len=0
  method isNotEmpty() : bool = len>0

  (* get topmost element but don't change what is stored *)
  method top() : 'a =
  begin
    arr.(len-1)
  end

  (* get topmost and remove it *)
  method pop() : 'a =
  begin
    len <- len - 1;
    arr.(len)
  end

  (* add a new topmost element *)
  method push (obj: 'a) : unit =
  begin
    if (len = (Array.length arr)) then (
      (* need to expand the array *)
      arr <- (growArray arr (len*2) null);
    );

    (* put new element into the array at the end *)
    arr.(len) <- obj;
    len <- len + 1;
  end

  (* get arbitrary element *)
  method elt (i: int) : 'a =
  begin
    arr.(i)
  end

  (* set arbitrary element *)
  method setElt (i: int) (v: 'a) : unit =
  begin
    arr.(i) <- v
  end

  (* iterate *)
  method iter (f: 'a -> unit) : unit =
  begin
    for i=0 to len-1 do
      (f (arr.(i)))
    done;
  end

  (* search and return the element index, or -1 for not found *)
  method findIndex (f: 'a -> bool) : int =
  begin
    (* ug.. must use tail recursion just so I can break early... *)
    let rec loop (i: int) : int =
    begin
      if (i > len-1) then (
        -1                 (* not found *)
      )
      else if (f (arr.(i))) then (
        i                  (* found *)
      )
      else (
        (loop (i+1))       (* keep looking *)
      )
    end in

    (loop 0)
  end

  (* search and return the element, or None *)
  method findOption (f: 'a -> bool) : 'a option =
  begin
    let idx:int = (self#findIndex f) in
    if (idx < 0) then (
      None                 (* not found *)
    )
    else (
      (Some arr.(idx))     (* found *)
    )
  end

  (* search *)
  method contains (f: 'a -> bool) : bool =
  begin
    ((self#findIndex f) >= 0)
  end


  (* just for 'swapWith' *)
  (* I tried making them 'private' but that only allows method calls
   * within the *same* object, not merely the same *type* object
   * as in C++ *)
  method (*private*) private_getArray() : 'a array = arr
  method (*private*) private_setLength(l: int) : unit = len <- l
  method (*private*) private_setArray(a: 'a array) : unit = arr <- a

  (* swap contents with another array stack *)
  method swapWith (obj: 'a tArrayStack) : unit =
  begin
    let tmpLen:int = len in
    let tmpArr:'a array = arr in

    len <- (obj#length());
    arr <- (obj#private_getArray());

    (obj#private_setLength tmpLen);
    (obj#private_setArray tmpArr);
  end

end


(* EOF *)
