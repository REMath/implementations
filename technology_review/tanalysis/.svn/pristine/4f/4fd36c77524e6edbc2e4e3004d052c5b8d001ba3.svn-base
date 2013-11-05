(* Frama-C journal generated at 05:29 the 29/05/2009 *)

(* Running *)
let start () =
 let () = Journal.run () in
 let () = Journal.apply "Cmdline.taint-analysis.enabled.set" true in
 let () = Journal.apply "Cmdline.taint-analysis.config-file.set" "../../../default.cfg" in
 let () = Journal.apply "Cmdline.taint-analysis.constr-config-file.set"
  "../../../default_constr.cfg" in
 let () = Journal.apply "Cmdline.taint-analysis.prepare-slice.set" true in
 let () = Cmdline.Files.add "cercuri.c" in
 let () = File.init_from_cmdline () in
 (* Finished *)
 Journal.finished ()

let () =
 try start ()
 with e -> Format.eprintf "Journal raised an exception: %s" (Printexc.to_string e)