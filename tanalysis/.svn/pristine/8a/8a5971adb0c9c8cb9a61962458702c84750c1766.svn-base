open Cil_types
open Cil


type refCountType = RefCount of int

type typeSize = TypeSize of refCountType * int

module TypeGetter(Param:sig
                        val fmt : Format.formatter
                        val debug : bool      
                        val info : bool     
                     end) = struct
                        
    module P = Printer.Printer(struct
                                    let fmt = Param.fmt
                                    let debug = Param.debug
                                    let info = Param.info
                                end)                    
    
    let rec is_structure typ =
        let do_named tinfo =
            is_structure tinfo.ttype
        in
        let do_comp compinfo =
            compinfo.cstruct
        in
        match typ with
            | TNamed (tinfo, _) -> do_named tinfo 
            | TComp (compinfo, _) -> do_comp compinfo
            | _ -> false
    
    let is_return_param typ = 
        Cil.isPointerType typ
    
    let rec get_actual_param expr =
        let do_get_actual_param_lvalue lvl =
            (* TODO: check this *)
            match lvl with
                | (Var vinfo, _) -> 
                    (match Cil.isPointerType vinfo.vtype with
                        | false -> None
                        | true -> Some vinfo)
                | _ -> None
        in
        let do_get_actual_param_cast typ cast_expr =
            match Cil.isPointerType typ with
                | false -> None
                | true -> get_actual_param cast_expr
        in
        let do_get_actual_param_unop typ un_expr =
            match Cil.isPointerType typ with
                | false -> None
                | true -> get_actual_param un_expr
        in
        let do_get_actual_param_binop typ left_expr right_expr =
            match Cil.isPointerType typ with
                | false -> None
                | true -> 
                    match get_actual_param left_expr with
                        | None -> get_actual_param right_expr
                        | Some vinfo -> Some vinfo 
        in
        let do_get_actual_param_addrof lvl =
            (* TODO: check this *)
            match lvl with
                | (Var vinfo, _) -> 
                    Some vinfo
                | _ -> 
                    None
        in
        let do_get_actual_param_startof lvl =
            (* TODO: check this *)
            match lvl with
                | (Var vinfo, _) -> Some vinfo
                | _ -> None
        in
        
        match expr with
            |   Const _ -> None
            |   SizeOf _ -> None
            |   SizeOfE _ -> None
            |   SizeOfStr _ -> None
            |   AlignOf _ -> None
            |   AlignOfE _ -> None
            |   Lval lvl -> do_get_actual_param_lvalue lvl
            |   CastE (typ, cast_expr) -> do_get_actual_param_cast typ cast_expr
            |   UnOp (_, un_expr, typ) -> do_get_actual_param_unop typ un_expr
            |   BinOp (_, left_expr, right_expr, typ) -> do_get_actual_param_binop typ left_expr right_expr
            |   AddrOf lvl -> do_get_actual_param_addrof lvl 
            |   StartOf lvl -> do_get_actual_param_startof lvl
            |   _ -> None
end

module TypeComparer(Param:sig
                        val fmt : Format.formatter
                        val debug : bool      
                        val info : bool     
                     end) = struct

    module P = Printer.Printer(struct
                                    let fmt = Param.fmt
                                    let debug = Param.debug
                                    let info = Param.info
                                end)

    (* TODO: Arch dependency *)
    let byte_size () = 1
    let short_size () = 2 * byte_size ()
    let word_size () = 4 * byte_size ()
    let long_size () = 4 * byte_size ()
    let longlong_size () = 8 * byte_size () 
    let float_size () = 4 * byte_size ()
    let double_size () = 8 * byte_size ()
    let longdouble_size () = 12 * byte_size ()
    let ptr_size () = 4 * byte_size ()
    let enum_size () = 4 * byte_size ()
    
    let rec do_get_type_size_int (RefCount ref_cnt) ikind =
        match ikind with
            | IChar -> TypeSize (RefCount ref_cnt, byte_size ())
            | ISChar -> TypeSize (RefCount ref_cnt, byte_size ())
            | IUChar -> TypeSize (RefCount ref_cnt, byte_size ())
            | IBool -> TypeSize (RefCount ref_cnt, word_size ())
            | IInt -> TypeSize (RefCount ref_cnt, word_size ()) 
            | IUInt -> TypeSize (RefCount ref_cnt, word_size ())
            | IShort -> TypeSize (RefCount ref_cnt, short_size ())
            | IUShort -> TypeSize (RefCount ref_cnt, short_size ())
            | ILong -> TypeSize (RefCount ref_cnt, long_size ())
            | IULong -> TypeSize (RefCount ref_cnt, long_size ())
            | ILongLong -> TypeSize (RefCount ref_cnt, longlong_size ())
            | IULongLong -> TypeSize (RefCount ref_cnt, longlong_size ())
    
    and do_get_type_size_float (RefCount ref_cnt) fkind =
        match fkind with
            | FFloat -> TypeSize (RefCount ref_cnt, float_size ())
            | FDouble -> TypeSize (RefCount ref_cnt, double_size ())
            | FLongDouble -> TypeSize (RefCount ref_cnt, longdouble_size ())
    
    and do_expand_named_type possible_named_typ =
        match possible_named_typ with
            | TNamed (tinfo, _) -> do_expand_named_type tinfo.ttype
            | _ -> possible_named_typ
    
    and do_get_type_size_struct compinfo =
        List.fold_left
            (fun size finfo ->
                let ftyp = do_expand_named_type finfo.ftype in
                match ftyp with
                    | TPtr _ -> size + ptr_size ()
                    | _ ->
                        (match get_type_size (RefCount 0) ftyp with
                            | TypeSize (RefCount 0, s) -> size + s
                            | TypeSize (RefCount _, s) -> size + ptr_size ()))  
            0 
            compinfo.cfields
    
    and do_get_type_size_union compinfo =
        List.fold_left
            (fun size finfo ->
                match get_type_size (RefCount 0) finfo.ftype with
                    | TypeSize (RefCount 0, s) -> if size > s then size else s
                    | TypeSize (RefCount _, s) -> if size > ptr_size () then size else ptr_size ())
            0 
            compinfo.cfields
            
    and do_get_type_size_comp (RefCount ref_cnt) compinfo =
        match compinfo.cstruct with
            | true -> TypeSize (RefCount ref_cnt, do_get_type_size_struct compinfo)
            | false -> TypeSize (RefCount ref_cnt, do_get_type_size_union compinfo)

    and do_get_type_size_ptr (RefCount ref_cnt) ptr_typ =
        let cnt = ref_cnt + 1 in
        get_type_size (RefCount cnt) ptr_typ
        
    and do_get_type_size_arr (RefCount ref_cnt) arr_typ =
        let cnt = ref_cnt + 1 in
        get_type_size (RefCount cnt) arr_typ

    and get_type_size (RefCount ref_cnt) typ =
        match typ with
            (* TODO: *)
            | TVoid _ -> 
                TypeSize (RefCount ref_cnt, 100000)
            | TInt (ikind, _) -> 
                do_get_type_size_int (RefCount ref_cnt) ikind
            | TFloat (fkind, _) -> 
                do_get_type_size_float (RefCount ref_cnt) fkind
            | TPtr (ptr_typ, _) -> 
                do_get_type_size_ptr (RefCount ref_cnt) ptr_typ
            (* TODO: Probably this isn't ok. What do we do if we have a fixed size array? *)
            | TArray (arr_typ, _, _) -> 
                do_get_type_size_arr (RefCount ref_cnt) arr_typ 
            | TNamed (tinfo, _) -> 
                get_type_size (RefCount ref_cnt) tinfo.ttype
            | TComp (compinfo, _) -> 
                do_get_type_size_comp (RefCount ref_cnt) compinfo
            | TEnum _ -> 
                TypeSize (RefCount ref_cnt, enum_size ())
            | _ -> 
                TypeSize (RefCount ref_cnt, 0)
    
    let rec get_expr_type_size (RefCount ref_cnt) expr  =
        let do_get_expr_type_size_const cnst =
            let do_get_expr_type_size_const_str () = 
                let cnt = ref_cnt + 1 in
                TypeSize (RefCount cnt, byte_size ())
            in
            let do_get_expr_type_size_const_wstr () = 
                let cnt = ref_cnt + 1 in
                TypeSize (RefCount cnt, longlong_size ())
            in
            match cnst with
                | CInt64 (_, ikind, _) -> do_get_type_size_int (RefCount ref_cnt) ikind
                | CStr _ -> do_get_expr_type_size_const_str ()
                | CWStr _ -> do_get_expr_type_size_const_wstr ()
                | CChr _ -> TypeSize (RefCount ref_cnt, byte_size ())
                | CReal (_, fkind, _) -> do_get_type_size_float (RefCount ref_cnt) fkind
                | CEnum _ -> TypeSize (RefCount ref_cnt, enum_size ())
        in
        let do_get_expr_type_size_lval lvl =
            let rec do_get_struct_union_field_type_size (finfo, off) =
                match off with
                    | NoOffset 
                        -> get_type_size (RefCount ref_cnt) finfo.ftype
                    | Field (inner_finfo, inner_off) 
                        -> do_get_struct_union_field_type_size (inner_finfo, inner_off)
                    | Index (idx_expr, inner_off) 
                        -> do_get_array_item_type_size finfo.ftype (idx_expr, inner_off)
            and do_get_array_item_type_size typ (idx_expr, off) =
                let do_get_array_item_type_size_no_offset () =
                    let cnt = ref_cnt - 1 in
                    get_type_size (RefCount cnt) typ
                in
                match off with
                    | NoOffset 
                        -> do_get_array_item_type_size_no_offset ()
                    | Field (inner_finfo, inner_off) 
                        -> do_get_struct_union_field_type_size (inner_finfo, inner_off)
                    | Index (inner_idx_expr, inner_off) 
                        -> do_get_array_item_type_size typ (inner_idx_expr, inner_off)
            in
            match lvl with
                | (Var vinfo, NoOffset) 
                    -> get_type_size (RefCount ref_cnt) vinfo.vtype
                | (Mem m_expr, NoOffset) 
                    -> get_expr_type_size (RefCount ref_cnt) m_expr
                | (_, Field (finfo, offset)) 
                    -> do_get_struct_union_field_type_size (finfo, offset)
                | (Var vinfo, Index (idx_expr, offset)) 
                    -> do_get_array_item_type_size vinfo.vtype (idx_expr, offset)
                | (Mem m_expr, Index (idx_expr, offset)) 
                    -> do_get_array_item_type_size 
                            (Cil.typeOf m_expr) 
                            (idx_expr, offset) 
        in
        let do_get_expr_type_size_addrOf lvl =
            let cnt = ref_cnt + 1 in
            get_expr_type_size (RefCount cnt) (Lval lvl) 
        in
        match expr with
            | Const cnst -> do_get_expr_type_size_const cnst
            | Lval lvl -> do_get_expr_type_size_lval lvl
            | SizeOf _ 
            | SizeOfE _ 
            | SizeOfStr _
            | AlignOf _
            | AlignOfE _ -> TypeSize (RefCount ref_cnt, word_size ())
            | UnOp (_, _, typ) -> get_type_size (RefCount ref_cnt) typ
            | BinOp (_, _, _, typ) -> get_type_size (RefCount ref_cnt) typ
            | CastE (typ, _) -> get_type_size (RefCount ref_cnt) typ
            | AddrOf lvl ->  do_get_expr_type_size_addrOf lvl
            | StartOf lvl -> do_get_expr_type_size_lval lvl
            | Info _ -> TypeSize (RefCount ref_cnt, 0)
    
    let check_type dest_type expr =
        (* TODO check casts *)
        true
        (* let TypeSize (RefCount src_ref_cnt, src_size) =    
            get_expr_type_size (RefCount 0) expr in
        let TypeSize (RefCount dst_ref_cnt, dst_size) = 
            get_type_size (RefCount 0) dest_type in
        match (dst_ref_cnt, src_ref_cnt) with
            | (x, y) when x > 0 && y == 0 -> true
            | (x, y) when x == y ->  dst_size <= src_size
            | _ ->  false *)
end
