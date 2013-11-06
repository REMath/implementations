functor ConorCheck ( structure ConorTopNeeds : CONORTOPNEEDS ) =

struct

local
    open ConorTopNeeds
    open ConorInductiveNeeds
    open Concrete

    exception not_app

		fun parse_app (Ref (Bd {bd=(_,s,_,_),...})) = (s,[],[])
		  | parse_app (App ((f,al),vl)) =
		    let
			val (s,bl,ul) = parse_app f
		    in
			(s,bl@al,vl@ul)
		    end
		  | parse_app _ = raise not_app

    fun Ref_s x = #1 (fEval (Ref_c x))


    exception missing

    fun z_assoc n (h::t) (g::s) = if (n=h) then g else z_assoc n t s
      | z_assoc _ _ _ = raise missing
in
    exception no_cycle_proof
    val check_stuff = ref {on=false, name=Bot, kill=Bot,
                           look=(fn (x:cnstr) => x)}
    fun checking (q_term,q_type) =
        let
            val {name=ch_type,kill=ch_kill,look=q_look,on=_} = !check_stuff
            val (ch_zero,ch_suc) =
                (case (#constructors (get_inductive_info ch_type))
                  of [z,s] => (Ref_s z,Ref_s s)
                   | _ => raise no_cycle_proof)
                handle not_inductive => failwith "bad checking configuration"
            val {name=eq_name,refl=eq_refl,sym=eq_sym,subst=eq_subst} =
                eq_info ()
            val (src_ind,chk_term,var_term) =
                case q_type
                 of (App ((Q,[T,X,Y]),_)) =>
                    if Q=eq_name then (T,X,Y) else raise no_cycle_proof
                  | _ => raise no_cycle_proof

            val _ = legoprint src_ind

            val info = get_inductive_info src_ind
                       handle not_inductive => raise no_cycle_proof
            val var_name = case var_term
                            of  (Ref (Bd {bd=(_,s,_,_),...})) => s
                             |  _ => raise no_cycle_proof
            fun rec_check (Ref (Bd {bd=(_,s,_,_),...})) =
                (s=(#name info))
              | rec_check (App ((f,_),_)) = rec_check f
              | rec_check (Bind (_,_,_,r)) = rec_check r
              | rec_check _ = false
            fun con_structure (Bind (_,_,r,t)) =
                let val (n,rest) = con_structure t
                in
                    if rec_check r then (n+1,n::rest)
                    else (n,0::rest)
                end
              | con_structure _ = (1,[])
            val con_structures = map ((#2) o con_structure) (#con_types info)

            val _ = map (map print) con_structures

            fun find_path x =
                let val (s,al,_) = parse_app x
                    val _ = legoprint x
                    val struc = z_assoc s (#constructors info) con_structures
                                handle missing => raise no_cycle_proof
                    fun search (0::t) (g::u) = search t u
                      | search (n::t) (g::u) =
                        ((case (q_look g)
                           of (Ref (Bd {bd=(_,v,_,_),...})) =>
                              if v=var_name then [(s,n)]
                              else raise no_cycle_proof
                            | x => (s,n)::(find_path x) )
                         handle no_cycle_proof => search t u)
                      | search _ _ = raise no_cycle_proof
                in  search struc al
                end
            val path = find_path (q_look chk_term)

            val depth = length path
            fun make_trick_type [_] = ch_type
              | make_trick_type (_::t) =
                Bind ((Sig,Vis),"",ch_type,make_trick_type t)
              | make_trick_type [] = raise no_cycle_proof
            val trick_type = make_trick_type path
            local
                fun last 1 t = t
                  | last n t = last (n-1) (Proj (Snd,t))
            in
                fun myproj n t =
                    if n=depth then last n t
                    else if n=1 then Proj (Fst,t)
                    else myproj (n-1) (Proj (Snd,t))
            end
            fun trick_rec_term n t =
                if n=depth then App ((ch_suc,[myproj 1 t]),[ShowNorm])
                else myproj (n+1) t
            fun con_tuplist n [] s = []
              | con_tuplist n ((s',k)::t) s =
                if s=s'
                    then (trick_rec_term n (Rel k))::(con_tuplist (n+1) t s)
                else ch_zero::(con_tuplist (n+1) t s)
            val con_tuplists = map (con_tuplist 1 path) (#constructors info)
            val arg =
                case (#elim_inst_type info)
                 of  Bind (_,_,a,_) => a
                  |  _ => raise no_cycle_proof
            fun mk_arg (Bind ((Pi,v),n,t,r)) =
                Bind ((Lda,v),n,t,mk_arg r)
              | mk_arg _ = trick_type
            val elim_scheme = App ((#elim_inst info,[mk_arg arg]),[ShowNorm])
            val con_things = (!toc) elim_scheme (* might need computes *)
            fun mk_con_thing res (Bind ((Pi,v),n,t,r)) =
                Bind ((Lda,v),n,t,mk_con_thing res r)
              | mk_con_thing res _ = Tuple (trick_type,res)
            fun mk_con_things [] _ = []
              | mk_con_things (g::u) (Bind (_,_,t,r)) =
                (mk_con_thing g t)::(mk_con_things u r)
              | mk_con_things _ _ = raise no_cycle_proof
            val trick_function =
                App ((elim_scheme,mk_con_things con_tuplists con_things),
                     map (fn _ => ShowNorm) (#constructors info))
            val resp_function = Bind ((Lda,Vis),"cyclic",#instance info,
                                      myproj 1 (App ((trick_function,
                                                     [Rel 1]),[ShowNorm])))
            val resp_proof =
                App ((eq_subst,
                [#instance info,chk_term,var_term,q_term,
                 Bind ((Lda,Vis),"trick",#instance info,
                       App ((eq_name,[ch_type,
                             App ((resp_function,[chk_term]),[ShowNorm]),
                             App ((resp_function,[Rel 1]),[ShowNorm])]),
                             [NoShow,ShowNorm,ShowNorm])),
                 App ((eq_refl,[ch_type,
                                App ((resp_function,[chk_term]),[ShowNorm])]),
                      [NoShow,ShowNorm])]),
                [NoShow,NoShow,NoShow,ShowNorm,ShowNorm,ShowNorm])
            val absurd_proof = App ((ch_kill,
                               [App ((resp_function,[var_term]),[ShowNorm]),
                                resp_proof]),[NoShow,ShowNorm])
        in  absurd_proof
        end
end

end
