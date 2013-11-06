open Basics ;;
open Varencoding ;;
open Zchaff ;;
open Cfg ;;

type cyktable = variable list array array
type wordtable = variable list array

let addToCYKTable table i j v =
  let vs = table.(i).(j) in
  table.(i).(j) <- v::vs


let addToWordTable table i v =
  let vs = table.(i) in
  table.(i) <- v::vs


let makeWordTable cfg k =
  let wordtable = Array.make k [] in

  for i=0 to k-1 do
    List.iter (fun t -> let v = T(t,i) in
                        if 1 = zchaff_GetVarAsgnment zchaff (getCode(v))
                        then addToWordTable wordtable i v)
              cfg.alphabet
  done;
  wordtable


let makeCYKTable cfg k =
  let cyktable = Array.make k (Array.make 0 []) in

  for i=0 to k-1 do
    cyktable.(i) <- Array.make (i+1) []
  done;

  for i=0 to k-1 do
    for j=0 to k-1 do
      for m=0 to 1 do
        List.iter (fun a -> let v = N(cfg,a,i,j,m) in
                            if 1 = getValue v
                            then addToCYKTable cyktable i j v)
                  cfg.nonterminals;
        for d=1 to 2 do
          List.iter (fun a -> let v = A(cfg,a,i,j,m,d) in
                              if 1 = getValue v
                              then addToCYKTable cyktable i j v)
                    cfg.nonterminals
        done
      done;
      for h=i to j-1 do
        List.iter (fun b -> List.iter (fun c -> let v = H(cfg,b,c,i,j,h) in
                                                if 1 = getValue v
                                                then addToCYKTable cyktable i j v;
                                                let v = H12(cfg,b,c,i,j,h) in
                                                if 1 = getValue v
                                                then addToCYKTable cyktable i j v;
                                                let v = H21(cfg,b,c,i,j,h) in
                                                if 1 = getValue v
                                                then addToCYKTable cyktable i j v) 
                                      cfg.nonterminals)
                  cfg.nonterminals;
        for h' = i to j-1 do
          List.iter (fun b -> 
            List.iter (fun c -> 
              List.iter (fun b' ->
                List.iter (fun c' -> let v = D(cfg,b,c,b',c',i,j,h,h') in
                                     if 1 = getValue v
                                     then addToCYKTable cyktable i j v) 
                          cfg.nonterminals)
                        cfg.nonterminals)
                      cfg.nonterminals)
                    cfg.nonterminals
        done
      done;
      List.iter (fun a -> let v = C(cfg,a,i,j) in
                          if 1 = getValue v
                          then addToCYKTable cyktable i j v)
                cfg.nonterminals
    done;
    let v = B(i) in
    if 1 = getValue v
    then addToCYKTable cyktable 0 i v
  done;

  cyktable


