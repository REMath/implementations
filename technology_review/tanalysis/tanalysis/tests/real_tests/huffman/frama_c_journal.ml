(* Frama-C journal generated at 09:18 the 28/05/2009 *)

(* Running *)
let start () =
 let () = Journal.run () in
 let () = Journal.apply "Cmdline.taint-analysis.enabled.set" true in
 let () = Journal.apply "Cmdline.taint-analysis.config-file.set" "../../../default.cfg" in
 let () = Journal.apply "Cmdline.taint-analysis.constr-config-file.set"
  "../../../default_constr.cfg" in
 let () = Journal.apply "Cmdline.taint-analysis.do-results.set" true in
 let () = Cmdline.Files.add "arbre.c" in
 let () = Cmdline.Files.add "bfile.c" in
 let () = Cmdline.Files.add "fap.c" in
 let () = Cmdline.Files.add "Occ.c" in
 let () = Cmdline.Files.add "prog6.c" in
 let () = File.init_from_cmdline () in
 (* Finished *)
 Journal.finished ()

let () =
 try start ()
 with e -> Format.eprintf "Journal raised an exception: %s" (Printexc.to_string e)