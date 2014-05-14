open Cil_types
open Cilutil
open Cil

(* reunites two lists recursively *)
let rec reunite comparator l1 l2 =
    match List.length l1 with
        | 0 
            -> l2
        | _ -> 
            let fst = List.hd l1 in
            let last = List.tl l1 in
            try 
                ignore (List.find (comparator fst) l2);
                reunite (comparator) last l2
            with Not_found ->
                reunite (comparator) last (fst::l2)

let get_function_by_name globals fname =
    try
        let GFun (func, _) = (List.find 
                            (fun g -> 
                                match g with
                                    | GFun (func, _) -> 
                                        func.svar.vname == fname
                                    | _ -> false)
                            globals) in
        Some func
    with Not_found -> None

let get_fundec_by_id globals fid =
    let GFun (func, _) = List.find
                            (fun g ->
                                match g with
                                    | GFun (func, _) -> 
                                        func.svar.vid = fid
                                    | _ -> false)
                            globals in
    func

(* Extracts the variable info from a pointer expression. *)
let extract_vinfo_from_ptr_expr expr =
    let rec _extract_vinfo_from_lval lvl =
        match lvl with
        | (Var vinfo, _) -> Some vinfo
        | (Mem exp, _) -> _extract_vinfo_from_ptr_expr exp
    and 
    _extract_vinfo_from_ptr_expr expr =
        match expr with
        | Const _ -> None
        | SizeOf _ -> None
        | SizeOfE _ -> None
        | SizeOfStr _ -> None
        | AlignOf _ -> None
        | AddrOf lvl -> _extract_vinfo_from_lval lvl
        | StartOf _ -> None
        | Lval lvl -> _extract_vinfo_from_lval lvl
        | UnOp (_, unop_expr, _) -> _extract_vinfo_from_ptr_expr unop_expr 
        | BinOp (_, expr1, expr2, _) 
            -> 
                let null_vinfo1 = _extract_vinfo_from_ptr_expr expr1 in
                let null_vinfo2 = _extract_vinfo_from_ptr_expr expr2 in
                (match null_vinfo1 with
                    | None -> null_vinfo2
                    | _ -> null_vinfo1)
        | _ -> None   
    in

    match _extract_vinfo_from_ptr_expr expr with
    | None -> raise Not_found
    | Some vinfo -> vinfo

let extract_lvalue_from_expr expr =
    let rec _extract_lvalue_from_expr expr =
	    match expr with
        | Const _ -> None
        | SizeOf _ -> None
        | SizeOfE _ -> None
        | SizeOfStr _ -> None
        | AlignOf _ -> None
        | AddrOf _ -> None
        | StartOf _ -> None
        | Lval lvl -> Some lvl
        | UnOp (_, unop_expr, _) -> _extract_lvalue_from_expr unop_expr 
        | BinOp (_, expr1, expr2, _) 
            -> 
                let null_vinfo1 = _extract_lvalue_from_expr expr1 in
                let null_vinfo2 = _extract_lvalue_from_expr expr2 in
                (match null_vinfo1 with
                    | None -> null_vinfo2
                    | _ -> null_vinfo1)
        | _ -> None   
    in
    
    match _extract_lvalue_from_expr expr with
    | None -> raise Not_found
    | Some lvl -> lvl

let get_lval_vinfo lval =
    match lval with
    | (Var vinfo, _) -> vinfo
    | (Mem exp, _) -> extract_vinfo_from_ptr_expr exp
