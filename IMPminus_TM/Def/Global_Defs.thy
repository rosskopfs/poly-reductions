theory Global_Defs
  imports "IMP_Minus.AExp"
begin

type_synonym label = nat
type_synonym pc = nat


subsection \<open>A modified list indexing method for GOTO programs\<close>
text \<open>The automatic transform from index of list to index of GOTO prog is done here\<close>
fun inth :: "'a list \<Rightarrow> nat \<Rightarrow> 'a" (infixl "!!" 100) where
  "[] !! i = undefined" |
  "(x # xs) !! i = (if i = 1 then x else xs !! (i - 1))"

lemma inth_mem[intro]:
  "0 < i \<Longrightarrow> i \<le> length xs \<Longrightarrow> xs !! i \<in> set xs"
  by (induction xs arbitrary: i) auto

lemma inth_append [simp]:
  "0 < i \<Longrightarrow> i \<le> length xs + length ys \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> ys \<noteq> [] \<Longrightarrow>
  (xs @ ys) !! i = (if i \<le> size xs then xs !! i else ys !! (i - size xs))" 
  apply (induction xs arbitrary: i) apply (auto simp: algebra_simps)
  apply (metis Suc_le_mono Suc_pred diff_is_0_eq list.size(3) neq0_conv trans_le_add1)
  by (smt (verit, ccfv_threshold) Suc_pred append_Nil diff_Suc_Suc diff_is_0_eq le0 list.size(3) neq0_conv)

lemma inth_append_in_fst_list [simp]:
  "0 < i \<Longrightarrow> i \<le> length xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> (xs @ ys) !! i = xs !! i"
  apply (induction xs arbitrary: i)
  apply auto
  by (metis Suc_le_mono Suc_pred diff_is_0_eq length_0_conv not_gr_zero)

end