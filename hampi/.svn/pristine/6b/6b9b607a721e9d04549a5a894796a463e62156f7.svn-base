open Cyktable ;;
open Basics ;;
open Varencoding ;;
open Parsetree ;;

let toLatex = function T(a,i) -> "$T^{\\verb#" ^ a ^ "#}_{" ^ string_of_int i ^ "}$"
      		   | N(_,v,i,j,m) -> "$N^{\\verb#" ^ v ^ "#," ^ string_of_int m ^ "}_{" ^ 
                                   string_of_int i ^ "," ^ string_of_int j ^ "}$"
  		   | H(_,b,c,i,j,h) -> "$H^{\\verb#" ^ b ^ "#,\\verb#" ^ c ^ "#}_{" ^ 
                                     string_of_int i ^ "," ^ string_of_int j ^ "," ^ string_of_int h ^ "}$"
  		   | H'(_,a,b,c,i,j) -> "$H'^{\\verb#" ^ a ^ "#,\\verb#" ^ b ^ "#,\\verb#" ^ c ^ "#}_{" ^ 
                                     string_of_int i ^ "," ^ string_of_int j ^ "}$"
      		    | H12(_,b,c,i,j,h) -> "${}^{12}H^{\\verb#" ^ b ^ "#,\\verb#" ^ c ^ "#}_{" ^ 
                                        string_of_int i ^ "," ^ string_of_int j ^ "," ^ string_of_int h ^ "}$"
      		    | H21(_,b,c,i,j,h) -> "${}^{21}H^{\\verb#" ^ b ^ "#,\\verb#" ^ c ^ "#}_{" ^ 
                                        string_of_int i ^ "," ^ string_of_int j ^ "," ^ string_of_int h ^ "}$"
      		    | B(i) -> "$B_{" ^ string_of_int i ^ "}$"
      		    | B'(i) -> "$B'_{" ^ string_of_int i ^ "}$"
		    | A(_,v,i,j,m,a) -> "$A^{\\verb#" ^ v ^ "#," ^ string_of_int m ^ "," ^
                                      string_of_int a ^ "}_{" ^ string_of_int i ^ "," ^ string_of_int j ^ "}$"
		    | C(_,a,i,j) -> "$C^{\\verb#" ^ a ^ "#}_{" ^ string_of_int i ^ "," ^ 
                                  string_of_int j ^ "}$"
		    | D(_,b,c,b',c',i,j,h,h') -> "$D^{\\verb#" ^ b ^ "#,\\verb#" ^ c ^ "#,\\verb#" 
                                               ^ b' ^ "#,\\verb#" ^ c' ^ "#}_{" ^ string_of_int i ^ "," ^ 
                                               string_of_int j ^ "," ^ string_of_int h ^ "," ^ string_of_int h' ^ "}$"


let latexHeader = 
  "\\documentclass{article}\n\\usepackage{parsetree}\n\\begin{document}\n\\begin{center}\n"

let latexFooter = 
  "\\end{center}\n\\end{document}\n"

let wordTableToTex wordtable =
  let l = Array.length wordtable in

  "\\begin{tabular}{|" ^ String.concat "|" (repeat "c" l) ^ "|}\\hline\n" ^
  String.concat " & " (List.map (fun vs -> String.concat "," (List.map toLatex vs)) 
                                (Array.to_list wordtable)) ^
  "\\\\\\hline\n\\end{tabular}\n"
   
let showWordTableInTex cfg k = wordTableToTex (makeWordTable cfg k)


let parseTreeToLatex t =
  let rec traverse = 
    function Leaf(a) -> "\\ptleaf{" ^ a ^ "}"
           | BinNode(n,t1,t2) -> "\\ptbeg\\ptnode{" ^ n ^ "}\n" ^ traverse t1 ^ "\n" ^ traverse t2 ^ "\\ptend\n"
           | Node(n,t) -> "\\ptbeg\\ptnode{" ^ n ^ "}" ^ traverse t ^ "\\ptend\n"
	   | Derivation(n,t) -> "\\ptbeg\\ptnode{" ^ n ^ "}\\pttritrue" ^ traverse t ^ "\\ptend\n"
	   | AmbDerivation(n,t) -> "\\ptbeg\\ptnode{" ^ n ^ "}\\pttritrue\\pttritrue" ^ traverse t ^ "\\ptend\n"
  in
  "\\ptbegtree\n" ^ traverse t ^ "\\ptendtree\n"
