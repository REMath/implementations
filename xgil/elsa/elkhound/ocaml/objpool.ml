(* objpool.ml *)
(* pool of allocated objects for explicit re-use *)
                                  
(* This object pool maintains a set of objects that are available
 * for use.  It must be given a way to create new objects. *)
class ['a] tObjectPool (allocFunc: unit -> 'a) =
object (self)
  (* implementation is just an array of elements that have been made
   * available for re-use; this should be regarded as private
   * inheritance, though I don't see how to do that in OCaml *)
  inherit (*PRIVATE*) ['a] Arraystack.tArrayStack (allocFunc ())

  (* ---- funcs ---- *)
  (* retrieve an object ready to be used; might return a pool element,
   * or if the pool is empty, will make a new element *)
  method alloc() : 'a =
  begin
    if (self#isNotEmpty()) then (
      (* just grab the topmost element in the pool stack *)
      (self#pop())
    )

    else (
      (* make a new object; I thought about making several at a time
       * but there seems little advantage.. *)
      (allocFunc ())
    )
  end

  (* return an object to the pool so it can be re-used *)
  method dealloc (obj: 'a) : unit =
  begin
    (* put the element into the stack *)
    (self#push obj);
  end
end


(* EOF *)
