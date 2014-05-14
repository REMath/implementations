(* Frama-C journal generated at 09:33 the 19/06/2009 *)

(* Running *)
let start () =
 let () = Journal.run () in
 let () = Cmdline.CppCommand.set "gcc -C -E -D_BSD_SOURCE -DDEBIAN -IEXT -I." in
 let () = Journal.apply "Cmdline.taint-analysis.enabled.set" true in
 let () = Journal.apply "Cmdline.taint-analysis.config-file.set" "../../../default.cfg" in
 let () = Cmdline.Files.add "_aux.c" in
 let () = Cmdline.Files.add "cmd1.c" in
 let () = Cmdline.Files.add "cmd2.c" in
 let () = Cmdline.Files.add "cmd3.c" in
 let () = Cmdline.Files.add "cmdtab.c" in
 let () = Cmdline.Files.add "collect.c" in
 let () = Cmdline.Files.add "edit.c" in
 let () = Cmdline.Files.add "fio.c" in
 let () = Cmdline.Files.add "getname.c" in
 let () = Cmdline.Files.add "head.c" in
 let () = Cmdline.Files.add "lex.c" in
 let () = Cmdline.Files.add "list.c" in
 let () = Cmdline.Files.add "main.c" in
 let () = Cmdline.Files.add "names.c" in
 let () = Cmdline.Files.add "popen.c" in
 let () = Cmdline.Files.add "quit.c" in
 let () = Cmdline.Files.add "send.c" in
 let () = Cmdline.Files.add "strings.c" in
 let () = Cmdline.Files.add "temp.c" in
 let () = Cmdline.Files.add "tty.c" in
 let () = Cmdline.Files.add "v7.local.c" in
 let () = Cmdline.Files.add "vars.c" in
 let () = Cmdline.Files.add "version.c" in
 let () = File.init_from_cmdline () in
 (* Finished *)
 Journal.finished ()

let () =
 try start ()
 with e -> Format.eprintf "Journal raised an exception: %s" (Printexc.to_string e)