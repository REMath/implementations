(** The logger module stores the log level specified with each of the ADs *)

(** Different log levels. Quiet means the bare minimum. Normal adds useful information and Debug everything else. *)
type log_level = Quiet | Normal | Debug

(** Type to identify the different ADs that can be specifically targeted for logging *)
type ad_ll = AgeLL | ArchitectureLL | CacheLL | FlagLL | MemLL | OctLL | RelCacheLL | SimpleOctLL | SimpleRelSetLL | StackLL | TraceLL | ValLL | IteratorLL

(** Map from ADs to their log level *)
module ADMap = Map.Make(struct type t = ad_ll let compare = Pervasives.compare end )

(** Static variables *)
let global_log_level = ref Quiet
let ad_log_level = ref ADMap.empty

(** Translates an string given by the user into an AD *)
let string_to_ad = function
	| "ageAD" -> AgeLL
	| "architectureAD" -> ArchitectureLL
	| "cacheAD" -> CacheLL
	| "flagAD" -> FlagLL
	| "memAD" -> MemLL
	| "octAD" -> OctLL
	| "relCacheAD" -> RelCacheLL
	| "simpleOctAD" -> SimpleOctLL
	| "simpleRelSetAD" -> SimpleRelSetLL
	| "stackAD" -> StackLL
	| "traceAD" -> TraceLL
	| "valAD" -> ValLL
	| "iterator" -> IteratorLL
	| _ -> failwith "AD not recognized"

(** Translates an string given by the user into a log level *)
let string_to_log_level = function
	| "normal" -> Normal
	| "quiet" -> Quiet
	| "debug" -> Debug
	| _ -> failwith "log level not recognized. Options: quiet, normal or debug"

(** Function specifiying logging dependencies between ADs *)
let ad_dependencies = function
	| ValLL -> [FlagLL]
	| _ -> []

(** Stores the log level of an AD, and updates the log level of its dependencies *)
let set_log_level ad level = 
	let rec update_dep ad =
		List.iter (fun x ->
			if ADMap.mem x !ad_log_level then
				()
			else begin
				ad_log_level := ADMap.add x Normal !ad_log_level;
				update_dep x
			end
			) (ad_dependencies ad); () in
	 ad_log_level := ADMap.add ad level !ad_log_level;
	 if level <> Quiet then update_dep ad else ()

(** Returns the log level for the specified abstract domain. *)
let get_log_level ad =
	try
		ADMap.find ad !ad_log_level
	with | Not_found -> !global_log_level

(** Sets the global log level with a string specified by the user *)
let set_global_ll string_level =
	global_log_level := (string_to_log_level string_level)

(** Sets the log level for a given ad. First parameter is the log level
  as a lowercase string and second one is the ad for which the log level
  is being specified (as string as well) *)
let set_ad_ll string_level string_ad = 
	set_log_level (string_to_ad string_ad) (string_to_log_level string_level)
