theory SS_To_ZERO_ONE
  imports "../XC_To_SS/XC_To_SS_aux"
begin

subsection "zero-one integer programming"

definition "zero_one_int_prog \<equiv> {(X, cs, B). \<forall>(as, s)\<in>X. 
  \<exists>xs. (\<forall>i<length xs. xs ! i \<in> {0, 1}) 
  \<and> (\<Sum>i<length as. as ! i * xs ! i) \<le> s \<and> length xs = length as 
  \<and> (\<Sum>i<length cs. cs ! i * xs ! i) \<ge> B \<and> length xs = length cs}"
(*The definition from the intractability book by Garey and Harrison*)

definition "ss_int_list_to_zero_one_int_prog \<equiv> \<lambda>(as, s). ({(as, s)}, as, s)"

definition "size_zero_one_int_prog \<equiv> \<lambda>(X, cs, B). (length cs + 1) * card X"


subsection "the reduction from subset sum int list to zero one integer programming is correct"

lemma ss_int_list_to_zero_one_int_prog_sound:
"(as, s) \<in> subset_sum_int_list \<Longrightarrow> ({(as, s)}, as, s) \<in> zero_one_int_prog"
unfolding subset_sum_int_list_def zero_one_int_prog_def 
by blast 

lemma ss_int_list_to_zero_one_int_prog_complete:
"({(as, s)}, as, s) \<in> zero_one_int_prog \<Longrightarrow> (as, s) \<in> subset_sum_int_list"
unfolding subset_sum_int_list_def zero_one_int_prog_def 
by auto

theorem is_reduction_ss_int_list_to_zero_one_int_prog:
"is_reduction ss_int_list_to_zero_one_int_prog subset_sum_int_list zero_one_int_prog"
unfolding is_reduction_def ss_int_list_to_zero_one_int_prog_def 
using ss_int_list_to_zero_one_int_prog_sound ss_int_list_to_zero_one_int_prog_complete 
by auto



end 