theory weighted_problems_poly 
  imports weighted_problems

begin

section "the type lifting between definitions is polynomial"

definition "ss_lift_to_int_alg x \<equiv> 
  do {
    RETURNT (ss_lift_to_int x)
  }"

definition "ss_lift_to_int_space n = n"
definition "ss_lift_to_int_time n = n"

subsection "proof"

lemma ss_lift_to_int_size:
"size_ss_int_list (ss_lift_to_int x) \<le> ss_lift_to_int_space (size_ss_list x)"
by (auto simp add: size_ss_int_list_def ss_lift_to_int_def 
  ss_lift_to_int_space_def size_ss_list_def split: prod.splits)

lemma ss_lift_to_int_refines:
"ss_lift_to_int_alg x \<le> SPEC (\<lambda>y. y = ss_lift_to_int x) (\<lambda>_. ss_lift_to_int_time (size_ss_list x))"
unfolding SPEC_def 
unfolding ss_lift_to_int_alg_def ss_lift_to_int_def 
apply (rule T_specifies_I)
apply (vcg' \<open>-\<close> rules: T_SPEC)
by auto

theorem ss_lift_to_int_is_polyred:
  "ispolyred ss_lift_to_int_alg subset_sum_list subset_sum_int_list size_ss_list size_ss_int_list"
unfolding ispolyred_def
  apply (rule exI[where x=ss_lift_to_int])
  apply (rule exI[where x=ss_lift_to_int_time])
  apply (rule exI[where x=ss_lift_to_int_space])
  apply safe
  subgoal
    using ss_lift_to_int_refines 
    by blast 
  subgoal 
    using ss_lift_to_int_size 
    by blast 
  subgoal 
    unfolding poly_def ss_lift_to_int_time_def 
    apply (intro exI[where x=2])
    by auto 
  subgoal 
    unfolding poly_def ss_lift_to_int_space_def 
    apply (intro exI[where x=2])
    by auto 
  subgoal 
    using is_reduction_ss_lift_to_int
    by blast 
  done 

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

section "the reduction from subset sum to knapsack is polynomial"

definition "ss_to_ks_alg \<equiv> \<lambda>(S, w, B).
  do {
    RETURNT (S, w, w, B, B)
  }"

definition "ss_to_ks_space n = n + 4"
definition "ss_to_ks_time n = n + 4"

subsection "proof"

lemma ss_to_ks_size:
"size_ks (ss_to_ks ss) \<le> ss_to_ks_space (size_SS ss)"
by (simp add: size_ks_def ss_to_ks_def ss_to_ks_space_def size_SS_def split: prod.splits)

lemma ss_to_ks_refines:
"ss_to_ks_alg ss \<le> SPEC (\<lambda>y. y = ss_to_ks ss) (\<lambda>_. ss_to_ks_time (size_SS ss))"
unfolding SPEC_def 
unfolding ss_to_ks_alg_def ss_to_ks_def 
apply (rule T_specifies_I)
apply(vcg' \<open>-\<close> rules: T_SPEC )
by auto

theorem ss_to_ks_is_polyred:
  "ispolyred ss_to_ks_alg subset_sum knapsack size_SS size_ks"
unfolding ispolyred_def
  apply(rule exI[where x=ss_to_ks])
  apply(rule exI[where x=ss_to_ks_time])
  apply(rule exI[where x=ss_to_ks_space])
  apply safe 
  subgoal 
    using ss_to_ks_refines
    by blast
  subgoal
    using ss_to_ks_size
    by blast 
  subgoal 
    unfolding poly_def ss_to_ks_time_def 
    apply(intro exI[where x=2])
    by auto
  subgoal 
    unfolding poly_def ss_to_ks_space_def
    apply(intro exI[where x=2])
    by auto
  subgoal
    using is_reduction_ss_to_ks
    by blast 
  done 

section "the reduction from subset sum int list to zero one integer programming is polynomial"

definition "ss_int_list_to_zero_one_int_prog_alg \<equiv> \<lambda>(as, s).
  do {
    RETURNT ({(as, s)}, as, s)
  }"

definition "ss_int_list_to_zero_one_int_prog_space n = n"
definition "ss_int_list_to_zero_one_int_prog_time n = 2 * n + 2"

subsection "proof"

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