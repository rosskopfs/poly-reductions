section \<open>Fundamental Definitions\<close>

subsection \<open>Reductions\<close>

theory Reductions
  imports Main
begin

definition is_reduction :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool" where
  "is_reduction f A B \<equiv> \<forall>a. a \<in> A \<longleftrightarrow> f a \<in> B "

lemma is_reduction_trans:
  assumes "is_reduction f A B" "is_reduction g B C"
  shows "is_reduction (g o f) A C"
  using assms unfolding is_reduction_def by auto


unbundle lifting_syntax

lemma transfer_is_reduction:
  assumes is_reduction_f: "is_reduction f (Collect P) (Collect Q)"
    and [transfer_rule]: "(R ===> (=)) P P'"
    and [transfer_rule]: "(R' ===> (=)) Q Q'"
    and [transfer_rule]: "(R ===> R') f f'"
    and transl_rel: "⋀x. R (t x) x"
  shows "is_reduction f' (Collect P') (Collect Q')"
proof -
  from transl_rel have [iff]: "⋀x. P' x ⟷ P (t x)"
    using assms(2) by (blast dest: rel_funD)
  have 1: "P' x ⟹ Q' (f' x)" for x
  proof - note [transfer_rule] = transl_rel[of x]
    assume "P' x"
    then have "P (t x)" by blast
    then have "Q (f (t x))"
      using is_reduction_f[unfolded is_reduction_def] by blast
    then show "Q' (f' x)" by transfer
  qed
  have 2: "Q' (f' x) ⟹ P' x" for x
  proof - note [transfer_rule] = transl_rel[of x]
    assume "Q' (f' x)"
    then have "Q (f (t x))" by transfer
    then have "P (t x)"
      using is_reduction_f[unfolded is_reduction_def] by blast
    then show "P' x" by blast
  qed
  from 1 2 show ?thesis unfolding is_reduction_def by blast
qed

end
