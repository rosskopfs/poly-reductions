theory SS_To_ZERO_ONE_Poly
  imports SS_To_ZERO_ONE
begin

definition "ss_int_list_to_zero_one_int_prog_alg \<equiv> \<lambda>(as, s).
  do {
    RETURNT ({(as, s)}, as, s)
  }"

definition "ss_int_list_to_zero_one_int_prog_space n = n"
definition "ss_int_list_to_zero_one_int_prog_time n = 2 * n + 2"

lemma ss_int_list_to_zero_one_int_prog_size:
"size_zero_one_int_prog (ss_int_list_to_zero_one_int_prog ss) \<le> ss_int_list_to_zero_one_int_prog_space (size_ss_int_list ss)"
by (auto simp add: size_zero_one_int_prog_def ss_int_list_to_zero_one_int_prog_def
 ss_int_list_to_zero_one_int_prog_space_def size_ss_int_list_def)

lemma ss_int_list_to_zero_one_int_prog_refines:
"ss_int_list_to_zero_one_int_prog_alg ss \<le> SPEC (\<lambda>y. y = ss_int_list_to_zero_one_int_prog ss)
  (\<lambda>_. ss_int_list_to_zero_one_int_prog_time (size_ss_int_list ss))"
unfolding SPEC_def
unfolding ss_int_list_to_zero_one_int_prog_alg_def ss_int_list_to_zero_one_int_prog_def
apply (rule T_specifies_I)
apply(vcg' \<open>-\<close> rules: T_SPEC )
by auto

theorem ss_int_list_to_zero_one_int_prog_is_polyred:
"ispolyred ss_int_list_to_zero_one_int_prog_alg subset_sum_int_list
    zero_one_int_prog size_ss_int_list size_zero_one_int_prog"
unfolding ispolyred_def
  apply(rule exI[where x=ss_int_list_to_zero_one_int_prog])
  apply(rule exI[where x=ss_int_list_to_zero_one_int_prog_time])
  apply(rule exI[where x=ss_int_list_to_zero_one_int_prog_space])
  apply safe
  subgoal
    using ss_int_list_to_zero_one_int_prog_refines
    by blast
  subgoal
    using ss_int_list_to_zero_one_int_prog_size
    by blast
  subgoal
    unfolding poly_def ss_int_list_to_zero_one_int_prog_time_def
    apply(intro exI[where x=2])
    by auto
  subgoal
    unfolding poly_def ss_int_list_to_zero_one_int_prog_space_def
    apply(intro exI[where x=2])
    by auto
  subgoal
    using is_reduction_ss_int_list_to_zero_one_int_prog
    by blast
  done


end