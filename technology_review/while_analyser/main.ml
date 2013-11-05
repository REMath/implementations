(*
 *  This file is part of WhileAnalyser
 *  Copyright (c)2005-2008 INRIA Rennes - Bretagne Atlantique
 *  David Pichardie <first.last@irisa.fr>
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *)

module Sign = Analyse.Make(EnvAbstractionNotRelational.Make(NumAbstractionSign.Make))

module Interval = Analyse.Make(EnvAbstractionNotRelational.Make(NumAbstractionInterval.Make))

type mode = Parse | Cfg | Sign | Interval

let mode = ref Interval
let target = ref ""

let args = [ 
  ("-parse", Arg.Unit (fun () -> mode := Parse) , "Print the program with labels");
  ("-cfg", Arg.Unit (fun () -> mode := Cfg) , "Print the control flow graph");
  ("-sign", Arg.Unit (fun () -> mode := Sign) , "Sign analysis");
  ("-interval", Arg.Unit (fun () -> mode := Sign) , "Interval analysis");
  ("-reduce", Arg.Unit (fun () -> EnvAbstractionNotRelational.reduction := true) , "Reduction operator for non-relational environment abstractions");
]

let _ =
  if not !Sys.interactive then
    begin
      Arg.parse args (fun s -> target := s) "usage: analyse <prog>" ;
      try 
	match !mode with
	  | Parse -> print_string (Print.print_program (Parse.parse !target))
	  | Cfg -> Cfg.print_cfg (Parse.parse !target)
	  | Sign ->
	      let p = Parse.parse !target in
	      let res = Sign.solve_and_print p in
		print_string (Print.print_program_with_res p res)
	  | Interval ->
	      let p = Parse.parse !target in
	      let res = Interval.solve_and_print p in
		print_string (Print.print_program_with_res p res)
      with x -> Printf.printf "uncaught exception %s\n" (Printexc.to_string x) 
    end

