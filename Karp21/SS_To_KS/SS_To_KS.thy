theory SS_To_KS
  imports "../XC_To_SS/XC_To_SS_aux"
begin

subsection "knapsack"

definition "knapsack \<equiv> {(S, w, b, W, B). finite S \<and> (\<exists>S' \<subseteq> S. sum w S' \<le> W \<and> sum b S' \<ge> B)}"

definition "ss_to_ks \<equiv> (\<lambda>(S, w, B). (S, w, w, B, B))"

definition "size_ks \<equiv> \<lambda>(S, w, b, W, B). card S"

subsection "the reduction from subset sum to knapsack is correct"

lemma ss_to_ks_sound:
"(S, w, B) \<in> subset_sum \<Longrightarrow> (S, w, w, B, B) \<in> knapsack"
  unfolding subset_sum_def is_subset_sum_def knapsack_def 
  by blast

lemma ss_to_ks_complete:
"(S, w, w, B, B) \<in> knapsack \<Longrightarrow> (S, w, B) \<in> subset_sum"
  unfolding subset_sum_def is_subset_sum_def knapsack_def 
  by auto 

theorem is_reduction_ss_to_ks:
"is_reduction ss_to_ks subset_sum knapsack"
  unfolding is_reduction_def ss_to_ks_def
  using ss_to_ks_sound ss_to_ks_complete 
  by fast

end