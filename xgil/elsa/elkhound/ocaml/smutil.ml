(* smutil.ml *)
(* some random utilities I think should be built in to the language *)

let isEmpty (lst: 'a list) : bool =
begin
  match lst with
  | _ :: _ -> false
  | _ -> true
end

let isNotEmpty (lst: 'a list) : bool =
begin
  (not (isEmpty lst))
end

let isNone (o: 'a option) : bool =
begin
  match o with
  | None -> true
  | _ -> false
end

let isSome (o: 'a option) : bool =
begin
  (not (isNone o))
end

let getSome (o: 'a option) : 'a =
begin
  match o with
  | None -> (failwith "getSome applied to None")
  | Some(v) -> v
end

(* true if 'o' is a Some, and it equals (==) 'v' *)
let someEquals (o: 'a option) (v: 'a) : bool =
begin
  match o with
  | None -> false
  | Some(v2) -> v2 == v
end

let xassertdb (b: bool) : unit =
begin
  if (not b) then (
    (failwith "(db) assertion failure")
  );
end

let xassert (b: bool) : unit =
begin
  if (not b) then (
    (failwith "assertion failure")
  );
end
