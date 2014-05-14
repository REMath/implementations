functor FunQuartermaster(structure Concrete : CONCRETE
                         structure Namespace : NAMESPACE) : QUARTERMASTER =
struct
local
  open Concrete
  open Namespace
  type 'a binder =
    bindSort * visSort * frzLocGlob * string list * string list * 'a

  exception quartermaster

  val Suppliers = ref ([] :
                       ((cnstr_c list) -> (cnstr_c * bool)) list)
  fun Supply tag =
      let fun s2 [] = raise quartermaster
            | s2 (h::t) = ((h tag) handle quartermaster => s2 t)
      in  s2 (!Suppliers)
      end

  fun labelTagName [] = "EMPTYTAG"
    | labelTagName [""] = "EMPTYSTRING"
    | labelTagName [s] = s
    | labelTagName (h::t) = h^"_"^(labelTagName t)

  fun magicTagName [] = "EMPTYTAG"
    | magicTagName [Ref_c ""] = "EMPTYSTRING"
    | magicTagName [Ref_c s] = s
    | magicTagName [_] = "TERM"
    | magicTagName ((Ref_c s)::t) = s^"_"^(magicTagName t)
    | magicTagName (_::t) = "TERM_"^(magicTagName t)

  val SLtoCL = map Ref_c
  fun CLtoSLo ((Ref_c s)::t) =
     (case (CLtoSLo t)
        of (SOME t') => SOME (s::t')
         | _ => NONE)
    | CLtoSLo [] = SOME []
    | CLtoSLo _ = NONE

  fun doMake tag = 
      let val stag = CLtoSLo tag
          val (term,store) = Supply tag
              handle quartermaster => failwith "No supplier!"
          val VT = fEval term
      in  case stag of NONE => term | SOME ss =>
          if   (activeProofState ()) orelse (not store)
          then term
          else let val nom = mkNameGbl (magicTagName tag)
                   val _ = extendCxtGbl (GenTag ss) (Let,Def) (UnFroz,Global)
                                        [] nom VT
               in  Ref_c nom
               end
      end

in
  type cnstr_c = cnstr_c
  val SLtoCL = SLtoCL
  val CLtoSLo = CLtoSLo

  exception quartermaster = quartermaster

  fun Label tag "" = Label tag (labelTagName tag)
    | Label tag name =
      ( ( (fEval (Ref_c name));
          (addLabel (tag,name));
          () )
        handle _ => failwith ("Could not label "^name) )
  fun Generate tag (Let,Def,frz_par_flg,deps,[nom],c) =
     (case spotLabel tag
        of SOME _ => ()
         | _ =>
           let val oldNSP = getNamespace ()
           in  let val _ = extendCxtGbl (GenTag tag) (Let,Def) frz_par_flg
                                        deps nom (fEval c)
                   val b = hd (getNamespace ())
               in  prnt_defn nom (ref_val b) (ref_typ b)
               end handle e => ((putNamespace oldNSP); (raise e))
           end)
    | Generate tag _ = ((doMake (SLtoCL tag));())

  fun Make tt =
     ((case CLtoSLo tt
         of SOME tag => (case spotLabel tag of SOME (x,_) => unEval x
                            | _ => raise Match)
          | _ => raise Match)
      handle Match => doMake tt)

  fun Register _ = failwith "Register not done yet"
end
end
