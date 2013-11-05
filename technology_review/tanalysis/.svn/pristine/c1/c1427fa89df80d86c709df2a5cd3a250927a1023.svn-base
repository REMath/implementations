open Cil_types
open Cil

module Printer(Param:sig
                    val dom_tree : stmt option Inthash.t 
                    val fmt : Format.formatter
                    val debug : bool
                    val info : bool
                 end) = struct
                   
    module P = Printer.Printer(struct
                                    let fmt = Param.fmt
                                    let debug = Param.debug
                                    let info = Param.info
                                end)
    let print_cfg func =
        let print_stmt stmt = 
            P.print () "\n\n SID: %d " stmt.sid;
            (match stmt.skind with 
                | (Instr _) -> P.print () "%s\n" "INSTR" 
                | (Return (_, _)) -> P.print () "%s\n" "RETURN"
                | (If (_, _, _, _)) -> P.print () "%s\n" "IF"
                | (Switch (_, _, _, _)) -> P.print () "%s\n" "SWITCH"
                | (Loop (_, _, _, _, _)) -> P.print () "%s\n" "LOOP"
                | (Block _) -> P.print () "%s\n" "BLOCK" 
                | (Break _) -> P.print () "%s\n" "BREAK"
                | (Continue _) -> P.print () "%s\n" "CONTINUE"
                | (Goto _) -> P.print () "%s\n" "GOTO"
                | _ -> P.print () "%s\n" "UNKNOWN"
                );
            P.print () "%s" "\n"
            
        in
        let print_sid_list name lst =
            P.print () "\n%s: " name;
            List.iter
                (fun s -> P.print () "%d, " s.sid)
                lst
        in 
        
        let stmts = func.sallstmts in
        List.iter 
            (fun stmt 
                ->
                    print_stmt stmt;
                    print_sid_list "SUCCESSORS" stmt.succs;
                    print_sid_list "PREDECESSORS" stmt.preds;
                    P.print () "\n%s" "DOMINATES:";
                    List.iter 
                        (fun s -> P.print () "%d, " s.sid)
                        (List.filter 
                            (fun s1 -> Dominators.dominates Param.dom_tree stmt s1)
                            stmts); 
                    P.print () "%s" "\n")
            stmts
end 
     