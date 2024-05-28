\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_To_IMP_Minus_Fun_Pattern_Setup
  imports
    HOL_To_IMP_Minus_Primitives
    "HOL-Library.Simps_Case_Conv"
begin

context HOL_To_IMP_Minus
begin

lemma case_nat_eq_if: "(case n of 0 \<Rightarrow> x | Suc x \<Rightarrow> f x) = (if n = 0 then x else f (n - 1))"
  unfolding Nitpick.case_nat_unfold by simp

end

paragraph \<open>Example application:\<close>

experiment
begin

interpretation HOL_To_IMP_Minus .

fun add_nat_pat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"add_nat_pat 0 0 z = z" |
"add_nat_pat 0 (Suc y) z = add_nat_pat 0 y (z + 1)" |
"add_nat_pat (Suc x) y z = add_nat_pat x y (z + 1)"
declare add_nat_pat.simps[simp del]

case_of_simps add_nat_pat_eq[unfolded case_nat_eq_if] : add_nat_pat.simps
compile_nat add_nat_pat_eq basename add_pat

HOL_To_IMP_Minus_func_correct add_nat_pat
  apply (terminates_with_res_IMP_Minus_start_base tailcall_def: add_pat_IMP_tailcall_def)
  apply (induction "(s ''add_pat.args.x1a'')" "(s ''add_pat.args.x2a'')" "(s ''add_pat.args.x3ba'')"
    arbitrary: s
    rule: add_nat_pat.induct)
  apply (simp only: sym[of 0 "s _" for s])
  apply (subst (2) add_pat_IMP_tailcall_def)
  apply (rule terminates_with_res_IMP_Tailcall_start)
  apply (terminates_with_res_step correctness:
    true_nat_IMP_Minus_func_correct
    false_nat_IMP_Minus_func_correct
    eq_nat_IMP_Minus_func_correct
    id_nat_IMP_Minus_func_correct
    sub_nat_IMP_Minus_func_correct
    not_nat_IMP_Minus_func_correct
    and_nat_IMP_Minus_func_correct
    min_nat_IMP_Minus_func_correct
    max_nat_IMP_Minus_func_correct
    le_nat_IMP_Minus_func_correct
  )+
  supply add_nat_pat_eq[simp] apply (STATE_interp_retrieve_key_eq)
  apply (terminates_with_res_step correctness:
    true_nat_IMP_Minus_func_correct
    false_nat_IMP_Minus_func_correct
    eq_nat_IMP_Minus_func_correct
    id_nat_IMP_Minus_func_correct
    add_nat_IMP_Minus_func_correct
    sub_nat_IMP_Minus_func_correct
    not_nat_IMP_Minus_func_correct
    and_nat_IMP_Minus_func_correct
    min_nat_IMP_Minus_func_correct
    max_nat_IMP_Minus_func_correct
    le_nat_IMP_Minus_func_correct
  )+
  apply terminates_with_res_tTail
  apply metis
  apply (terminates_with_res_step correctness:
    true_nat_IMP_Minus_func_correct
    false_nat_IMP_Minus_func_correct
    eq_nat_IMP_Minus_func_correct
    id_nat_IMP_Minus_func_correct
    add_nat_IMP_Minus_func_correct
    sub_nat_IMP_Minus_func_correct
    not_nat_IMP_Minus_func_correct
    and_nat_IMP_Minus_func_correct
    min_nat_IMP_Minus_func_correct
    max_nat_IMP_Minus_func_correct
    le_nat_IMP_Minus_func_correct
  )+
  apply terminates_with_res_tTail
  apply metis
  apply (subst (2) add_pat_IMP_tailcall_def)
  apply (rule terminates_with_res_IMP_Tailcall_start)
  apply (terminates_with_res_step correctness:
    true_nat_IMP_Minus_func_correct
    false_nat_IMP_Minus_func_correct
    eq_nat_IMP_Minus_func_correct
    id_nat_IMP_Minus_func_correct
    sub_nat_IMP_Minus_func_correct
    not_nat_IMP_Minus_func_correct
    and_nat_IMP_Minus_func_correct
    min_nat_IMP_Minus_func_correct
    max_nat_IMP_Minus_func_correct
    le_nat_IMP_Minus_func_correct
  )+
  apply (STATE_interp_retrieve_key_eq)
  apply (terminates_with_res_step correctness:
    true_nat_IMP_Minus_func_correct
    false_nat_IMP_Minus_func_correct
    eq_nat_IMP_Minus_func_correct
    id_nat_IMP_Minus_func_correct
    add_nat_IMP_Minus_func_correct
    sub_nat_IMP_Minus_func_correct
    not_nat_IMP_Minus_func_correct
    and_nat_IMP_Minus_func_correct
    min_nat_IMP_Minus_func_correct
    max_nat_IMP_Minus_func_correct
    le_nat_IMP_Minus_func_correct
  )+
  apply terminates_with_res_tTail
  apply (simp only: STATE_eq interp_update_state_eq interp_state_State_eq)
  subgoal premises p for _ s
  (*instantiate with current state, prove that arguments are equal to arguments of HOL recursive
  call, then apply*)
  thm p(1)
  oops

end

end
