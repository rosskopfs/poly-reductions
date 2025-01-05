theory SS_To_PART_poly
  imports "../XC_To_SS/XC_To_SS_aux"  "../Reductions" "SS_To_PART"
begin

section "the reduction from subset sum to number partition is polynomial"

subsection "definitions"

definition "mop_check_not_greater_eq \<equiv> \<lambda>(as, s). SPECT [s \<le> sum ((!) as) {..<length as} \<mapsto> 1]"
definition "mop_cons_new_sum \<equiv> \<lambda>(as, s). SPEC (\<lambda>as'. as' = (sum ((!) as) {..<length as} + 1 - s) # (s + 1) # as) (\<lambda>_. 3 * length as + 3 + 2)"
(* 2*length for indexing and addition*)

definition "ss_list_to_part_alg \<equiv> \<lambda>(as, s).
  do {
    b \<leftarrow> mop_check_not_greater_eq (as, s);
    if b
    then do {
      as' \<leftarrow> mop_cons_new_sum (as, s);
      RETURNT as'
    } 
    else do {
      RETURNT [1]
    }
  }"

definition "ss_list_to_part_space n = n + 3"
definition "ss_list_to_part_time n = 1 + 3*n + 3 + 2"

subsection "proof"

lemma ss_list_to_part_size:
"size_part (ss_list_to_part ss) \<le> ss_list_to_part_space (size_ss_list ss)"
by (auto simp add: size_part_def ss_list_to_part_def ss_list_to_part_space_def 
  size_ss_list_def split: prod.splits)

lemma ss_list_to_part_refines:
"ss_list_to_part_alg ss \<le> SPEC (\<lambda>y. y = ss_list_to_part ss) (\<lambda>_. ss_list_to_part_time (size_ss_list ss))"
unfolding SPEC_def 
unfolding ss_list_to_part_alg_def ss_list_to_part_def ss_list_to_part_time_def
mop_check_not_greater_eq_def mop_cons_new_sum_def
apply (rule T_specifies_I)
apply (vcg' \<open>-\<close> rules: T_SPEC)
by (auto simp add: one_enat_def size_ss_list_def)

theorem ss_list_to_part_is_polyred:
  "ispolyred ss_list_to_part_alg subset_sum_list part size_ss_list size_part"
unfolding ispolyred_def
  apply(rule exI[where x=ss_list_to_part])
  apply(rule exI[where x=ss_list_to_part_time])
  apply(rule exI[where x=ss_list_to_part_space])
  apply safe 
  subgoal 
    using ss_list_to_part_refines 
    by blast
  subgoal
    using ss_list_to_part_size
    by blast 
  subgoal 
    unfolding poly_def ss_list_to_part_time_def
    apply(intro exI[where x=2]) 
    by auto
  subgoal 
    unfolding poly_def ss_list_to_part_space_def
    apply(intro exI[where x=2])
    by auto
  subgoal
    using is_reduction_ss_list_to_part
    by blast 
  done 
end