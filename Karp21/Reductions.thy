section \<open>Reductions\<close>
theory Reductions
  imports Main
begin

definition is_reduction :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool" where
  "is_reduction f A B \<equiv> \<forall>a. a \<in> A \<longleftrightarrow> f a \<in> B "

lemma is_reductionI:
  assumes "\<And>a. a \<in> A \<Longrightarrow> f a \<in> B"
  and "\<And>a. f a \<in> B \<Longrightarrow> a \<in> A"
  shows "is_reduction f A B"
  using assms unfolding is_reduction_def by auto

lemma is_reductionE:
  assumes "is_reduction f A B"
  obtains "\<And>a. a \<in> A \<Longrightarrow> f a \<in> B" "\<And>a. f a \<in> B \<Longrightarrow> a \<in> A"
  using assms unfolding is_reduction_def by auto

lemma is_reduction_id: "is_reduction id A A"
  by (intro is_reductionI) auto

lemma is_reduction_trans:
  assumes "is_reduction f A B" "is_reduction g B C"
  shows "is_reduction (g o f) A C"
  using assms by (intro is_reductionI) (auto elim!: is_reductionE)

unbundle lifting_syntax

lemma transfer_is_reduction_Collect:
  assumes is_reduction_f: "is_reduction f (Collect P) (Collect Q)"
  and [transfer_rule]: "(R ===> (\<longleftrightarrow>)) P P'"
  and [transfer_rule]: "(R' ===> (\<longleftrightarrow>)) Q Q'"
  and [transfer_rule]: "(R ===> R') f f'"
  and transl_rel: "\<And>x. R (t x) x"
  shows "is_reduction f' (Collect P') (Collect Q')"
proof -
  from transl_rel have [iff]: "\<And>x. P' x \<longleftrightarrow> P (t x)"
    using assms(2) by (blast dest: rel_funD)
  have "Q' (f' x)" if "P' x" for x
  proof -
    note [transfer_rule] = transl_rel[of x]
    from that have "P (t x)" by blast
    then have "Q (f (t x))" using is_reduction_f by (auto elim: is_reductionE)
    then show "Q' (f' x)" by transfer
  qed
  moreover have "P' x" if "Q' (f' x)" for x
  proof - note [transfer_rule] = transl_rel[of x]
    from that have "Q (f (t x))" by transfer
    then have "P (t x)" using is_reduction_f by (auto elim: is_reductionE)
    then show "P' x" by blast
  qed
  ultimately show ?thesis by (auto intro: is_reductionI)
qed

end
