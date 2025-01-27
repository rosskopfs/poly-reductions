theory SS_To_KS_Poly
  imports SS_To_KS
begin

definition "ss_to_ks_alg \<equiv> \<lambda>(S, w, B).
  do {
    RETURNT (S, w, w, B, B)
  }"

definition "ss_to_ks_space n = n + 4"
definition "ss_to_ks_time n = n + 4"

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

end