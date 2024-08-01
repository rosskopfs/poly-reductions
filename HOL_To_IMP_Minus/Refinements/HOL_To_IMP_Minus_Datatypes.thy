\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_To_IMP_Minus_Datatypes
  imports
    HOL_To_HOL_Nat.HOL_To_HOL_Nat_Basics
    HOL_To_IMP_Minus_Primitives
begin

locale HOL_To_HOL_Nat =
  notes transport_eq_id.partial_equivalence_rel_equivalenceI[per_intro del]
  and transport_eq_restrict_id.partial_equivalence_rel_equivalence[per_intro del]
begin

case_of_simps append_eq_case : append.simps
function_compile_nat append_eq_case

case_of_simps rev_eq_case : rev.simps
function_compile_nat rev_eq_case

end
context HOL_To_IMP_Minus
begin

(*dummy stubs; need to compile fst_nat, snd_nat, pair_nat*)
(*then we could compile constructors and automatically generated functions:*)
thm Cons_nat_def

declare_compiled_const fst_nat
  return_register "fst.ret"
  argument_registers "fst.args.x"
  compiled suc_IMP

declare_compiled_const snd_nat
  return_register "fst.ret"
  argument_registers "fst.args.x"
  compiled suc_IMP

declare_compiled_const Cons_nat
  return_register "fst.ret"
  argument_registers "fst.args.x" "fst.args.y"
  compiled suc_IMP

declare_compiled_const Pure.type
  return_register "fst.ret"
  argument_registers
  compiled suc_IMP

context
  fixes xs' ys' :: "('a :: compile_nat) list"
  assumes rels: "Rel_nat xs xs'" "Rel_nat xs ys'"
begin

lemmas test = HOL_To_HOL_Nat.append_nat_eq_unfolded[OF rels, unfolded case_list_nat_def]
(*ooops*)
(* compile_nat test  *)

end

end

end
