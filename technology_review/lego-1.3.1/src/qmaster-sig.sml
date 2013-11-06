local
  type 'a binder =
    bindSort * visSort * frzLocGlob * string list * string list * 'a
in
signature QUARTERMASTER =
sig
  type cnstr_c
  val Label : (string list) -> string -> unit
  val Generate : (string list) -> (cnstr_c binder) -> unit
  val Make : (cnstr_c list) -> cnstr_c
  exception quartermaster
  val Register : ((cnstr_c list) -> (cnstr_c * bool)) -> unit
  val SLtoCL : (string list) -> (cnstr_c list)
  val CLtoSLo : (cnstr_c list) -> (string list) option
end
end
