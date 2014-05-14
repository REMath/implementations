open Cil
open Cil_types
open TaintGamma

class print stmt_hash = object(self)
    inherit defaultCilPrinterClass as super

    method pAnnotatedStmt next fmt s =
        let sid = s.sid in
        (if Inthash.mem stmt_hash sid then
            super#pGlobal fmt (GText "/*BEST_PATH*/"));
        super#pAnnotatedStmt next fmt s
end