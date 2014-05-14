(* tobjpool.ml *)
(* test program for objpool.ml *)

open Objpool
                     
let counter : int ref = ref 0
   
(* my "allocator" will just return successive integers, which my testing
 * harness can then manipulate like I would addresses in C *)
let allocator() : int =
begin
  (incr counter);
  (!counter - 1);
end

let main() : unit =
begin
  let pool : int tObjectPool = (new tObjectPool allocator) in
  
  (* allocate objects 1 through 10 *)
  for i = 1 to 10 do
    (Printf.printf "alloc: %d\n" (pool#alloc()));
  done;

  (* free the even ones *)
  for i = 1 to 5 do
    let addr:int = i*2 in
    (pool#dealloc addr);
    (Printf.printf "dealloc: %d\n" addr);
  done;

  (* allocate 10 more; should get the evens again, plus 11-15 *)
  for i = 1 to 10 do
    let addr:int = (pool#alloc()) in
    (Printf.printf "alloc: %d\n" addr);
    if (addr < 10 && ((addr mod 2) = 1)) then (
      (* this would mean it had somehow given us one of the low-valued
       * odd numbers, but those are still in use! *)
      (failwith "allocator bug");
    );
  done;

end
;;

Printexc.catch main()
;;


(* EOF *)
