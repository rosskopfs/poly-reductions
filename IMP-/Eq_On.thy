\<^marker>\<open>creator "Fabian Huch"\<close>
theory Eq_On
  imports Main
begin

definition eq_on :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> bool"
  ("(_ =/ _/ on _)" [50,0,50] 50) where
"f = g on S \<equiv> \<forall>x\<in>S. f x = g x"

lemma eq_onI[intro,simp]:
  assumes "\<And>x. x \<in> S \<Longrightarrow> f x = g x"
  shows "f = g on S"
  unfolding eq_on_def using assms by simp

lemma eq_onD[dest]:
  assumes "f = g on S"
  and "x\<in>S"
  shows "f x = g x"
  using assms unfolding eq_on_def by simp

lemma eq_onE:
  assumes "f = g on S"
      and "x\<in>S"
  obtains "f x = g x"
  using assms by auto

lemma eq_on_subset[intro]:
  assumes "f = g on S"
      and "S' \<subseteq> S"
    shows "f = g on S'"
  using assms by blast

lemma eq_on_feq1[intro]:
  assumes "f = g on S"
    and "\<forall>x \<in> S. f x = f' x"
  shows "f' = g on S"
  using assms by fastforce

lemma eq_on_feq2[intro]:
  assumes "f = g on S"
    and "\<forall>x \<in> S. g x = g' x"
  shows "f = g' on S"
  using assms by fastforce

lemma eq_on_fupd1[simp]:
  assumes "f = g on S"
    and "x \<notin> S"
  shows "f(x:=y) = g on S"
  using assms by fastforce

lemma eq_on_fupd2[simp]:
  assumes "f = g on S"
    and "x \<notin> S"
  shows "f = g(x:=y) on S"
  using assms by fastforce

end
