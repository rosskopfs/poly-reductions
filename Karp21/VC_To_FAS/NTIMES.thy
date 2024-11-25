theory NTIMES                                                          
  imports "HOL-Eisbach.Eisbach"
begin

(* code from: https://stackoverflow.com/a/58216879 
   Author: MercedesJones
   CC BY-SA 4.0: https://creativecommons.org/licenses/by-sa/4.0/
*)

ML \<open>
infixr 2 TIMES
fun 0 TIMES _ = all_tac
  | n TIMES tac = tac THEN (n - 1) TIMES tac
\<close>
method_setup ntimes = \<open>
  Scan.lift Parse.nat -- Method.text_closure >>
  (fn (n, closure) => fn ctxt => fn facts => 
    let
      val tac = method_evaluate closure ctxt facts
    in
     SIMPLE_METHOD (n TIMES tac) facts
    end)
\<close>
end