Require FirstGotoAnalysis.
Require EvalGoto.

Set Extraction AccessOpaque.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Require IntervalDomain.
Extract Constant IntervalDomain.Interval.next_larger => "IntervalDomainaux.next_larger".
Extract Constant IntervalDomain.Interval.next_smaller => "IntervalDomainaux.next_smaller".

Extraction Blacklist List String Int.

Require DebugAbMachineNonrel.
Extract Constant DebugAbMachineNonrel.print_string => "fun x -> print_endline (Camlcoq.camlstring_of_coqstring x)".
Extract Constant DebugAbMachineNonrel.print => "fun s (x: 'a) -> print_string s; x".

Cd "extraction".
Separate Extraction
  FirstGotoAnalysis AbCfg AbCfg2 GotoSem
  DebugAbMachineNonrel.print_string
  EvalGoto.run
  Goto.decode_instr
  Integers.Int64
.

Print Assumptions GotoAnalysis.vp_safety_check.
