\<^marker>\<open>contributor "Nico Lintner"\<close>
\<^marker>\<open>contributor "Kevin Kappelmann"\<close>
theory SAT_Definition
  imports Main
begin

subsection \<open>Definition of SAT\<close>

datatype 'a lit = Pos 'a | Neg 'a

type_synonym 'a sat = "'a lit set list"

definition models_lit :: "('a \<Rightarrow> bool) \<Rightarrow> 'a lit \<Rightarrow> bool" ("_\<up>" 60) where
  "models_lit \<sigma> \<equiv> \<lambda>l. case l of Pos x \<Rightarrow> \<sigma> x | Neg x \<Rightarrow> \<not> \<sigma> x"

lemma models_lit_PosI [intro!]:
  assumes "\<sigma> v"
  shows "(\<sigma>\<up>) (Pos v)"
  using assms unfolding models_lit_def by auto

lemma models_lit_NegI [intro!]:
  assumes "\<not>(\<sigma> v)"
  shows "(\<sigma>\<up>) (Neg v)"
  using assms unfolding models_lit_def by auto

lemma models_lit_PosD [dest!]:
  assumes "(\<sigma>\<up>) (Pos v)"
  shows "\<sigma> v"
  using assms unfolding models_lit_def by auto

lemma models_lit_NegD [dest!]:
  assumes "(\<sigma>\<up>) (Neg v)"
  shows "\<not>(\<sigma> v)"
  using assms unfolding models_lit_def by auto

lemma models_lit_eq_cases: "models_lit \<sigma> = (\<lambda>l. case l of Pos x \<Rightarrow> \<sigma> x | Neg x \<Rightarrow> \<not>(\<sigma> x))"
  by (intro ext) (auto split: lit.splits)

definition "models_clause \<sigma> cls \<equiv> \<exists>l \<in> cls. (\<sigma>\<up>) l"

lemma models_clauseI [intro]:
  assumes "l \<in> cls"
  and "(\<sigma>\<up>) l"
  shows "models_clause \<sigma> cls"
  using assms unfolding models_clause_def by auto

lemma models_clauseE [elim]:
  assumes "models_clause \<sigma> cls"
  obtains l where "l \<in> cls" "(\<sigma>\<up>) l"
  using assms unfolding models_clause_def by auto

definition models :: "('a \<Rightarrow> bool) \<Rightarrow> 'a sat \<Rightarrow> bool" (infixl "\<Turnstile>" 55) where
  "\<sigma> \<Turnstile> F \<equiv> \<forall>cls \<in> set F. models_clause \<sigma> cls"

lemma modelsI [intro]:
  assumes "\<And>cls. cls \<in> set F \<Longrightarrow> models_clause \<sigma> cls"
  shows "\<sigma> \<Turnstile> F"
  using assms unfolding models_def by auto

lemma modelsE [elim]:
  assumes "\<sigma> \<Turnstile> F"
  obtains "\<And>cls. cls \<in> set F \<Longrightarrow> models_clause \<sigma> cls"
  using assms unfolding models_def by auto

definition sat :: "'a sat \<Rightarrow> bool" where
  "sat F \<equiv> \<exists>\<sigma>. \<sigma> \<Turnstile> F"

lemma satI [intro]:
  assumes "\<sigma> \<Turnstile> F"
  shows "sat F"
  using assms unfolding sat_def by auto

lemma satE [elim]:
  assumes "sat F"
  obtains \<sigma> where "\<sigma> \<Turnstile> F"
  using assms unfolding sat_def by auto

definition "is_n_clause n C \<equiv> card C = n"

lemma is_n_clause_iff [iff]: "is_n_clause n C \<longleftrightarrow> card C = n"
  unfolding is_n_clause_def by simp

lemma finite_if_ne_zero_is_n_clause:
  assumes "is_n_clause n C"
  and "n \<noteq> 0"
  shows "finite C"
  using assms using card.infinite by fastforce

definition "is_n_sat n F \<equiv> \<forall>cls \<in> set F. is_n_clause n cls"

lemma is_n_satI [intro]:
  assumes "\<And>cls. cls \<in> set F \<Longrightarrow> is_n_clause n cls"
  shows "is_n_sat n F"
  using assms unfolding is_n_sat_def by auto

lemma is_n_satE [elim]:
  assumes "is_n_sat n F"
  obtains "\<And>cls. cls \<in> set F \<Longrightarrow> is_n_clause n cls"
  using assms unfolding is_n_sat_def by auto

lemma finite_if_mem_if_ne_zero_is_n_clause:
  assumes "is_n_sat n F"
  and "n \<noteq> 0"
  and "cls \<in> set F"
  shows "finite cls"
  using assms finite_if_ne_zero_is_n_clause by auto

definition "three_cnf_sat_pred F \<equiv> is_n_sat 3 F \<and> sat F"

lemma three_cnf_sat_predI [intro]:
  assumes "is_n_sat 3 F"
  and "sat F"
  shows "three_cnf_sat_pred F"
  using assms unfolding three_cnf_sat_pred_def by auto

lemma three_cnf_sat_predE [elim]:
  assumes "three_cnf_sat_pred F"
  obtains "is_n_sat 3 F" "sat F"
  using assms unfolding three_cnf_sat_pred_def by auto

definition "three_cnf_sat \<equiv> {F. three_cnf_sat_pred F}"

lemma three_cnf_sat_eq_Collect_three_cnf_sat_pred [simp]: "three_cnf_sat = {F. three_cnf_sat_pred F}"
  unfolding three_cnf_sat_def by simp

end
