(* Copyright (c) 2013, IMDEA Software Institute.             *)
(* See ./LICENSE for authorship and licensing information    *)

(** The logger module stores the log level specified with each of the ADs *)

(** Different log levels. Quiet means the bare minimum. Normal adds useful information and Debug everything else. *)
type log_level = Quiet | Normal | Debug

(** Type to identify the different ADs that can be specifically targeted for logging *)
type ad_ll =
    AgeLL
  | ArchitectureLL
  | CacheLL
  | FlagLL
  | MemLL
  | OctLL
  | RelCacheLL
  | SimpleOctLL
  | SimpleRelSetLL
  | StackLL
  | TraceLL
  | ValLL
  | IteratorLL

(** Returns the log level for the specified abstract domain. *)
val get_log_level : ad_ll -> log_level

(** Sets the global log level with a string specified by the user *)
val set_global_ll : string -> unit

(** Sets the log level for a given ad. First parameter is the log level
  as a lowercase string and second one is the ad for which the log level
  is being specified (as string as well) *)
val set_ad_ll : string -> string -> unit
