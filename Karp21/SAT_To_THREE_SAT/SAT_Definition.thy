\<^marker>\<open>contributor "Nico Lintner"\<close>
\<^marker>\<open>contributor "Kevin Kappelmann"\<close>
section\<open>Definition of (CNF) SAT\<close>
theory SAT_Definition
  imports Main
begin

datatype 'a lit = Pos 'a | Neg 'a

fun flip_lit where
  "flip_lit (Pos a) = (Neg a)"
| "flip_lit (Neg a) = (Pos a)"

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

definition "sat_pred F \<equiv> \<exists>\<sigma>. \<sigma> \<Turnstile> F"

lemma sat_predI [intro]:
  assumes "\<sigma> \<Turnstile> F"
  shows "sat_pred F"
  using assms unfolding sat_pred_def by auto

lemma sat_predE [elim]:
  assumes "sat_pred F"
  obtains \<sigma> where "\<sigma> \<Turnstile> F"
  using assms unfolding sat_pred_def by auto

definition "sat \<equiv> {F. sat_pred F}"

lemma sat_eq_Collect_sat_pred [simp]: "sat = {F. sat_pred F}"
  unfolding sat_def by simp

definition "is_fin_sat F \<equiv> \<forall>cls \<in> set F. finite cls"

lemma is_fin_satI [intro]:
  assumes "\<And>cls. cls \<in> set F \<Longrightarrow> finite cls"
  shows "is_fin_sat F"
  using assms unfolding is_fin_sat_def by auto

lemma is_fin_satE [elim]:
  assumes "is_fin_sat F"
  obtains "\<And>cls. cls \<in> set F \<Longrightarrow> finite cls"
  using assms unfolding is_fin_sat_def by auto

definition "fin_sat_pred F \<equiv> sat_pred F \<and> is_fin_sat F"

lemma fin_sat_predI [intro]:
  assumes "is_fin_sat F"
  and "sat_pred F"
  shows "fin_sat_pred F"
  using assms unfolding fin_sat_pred_def by auto

lemma fin_sat_predE [elim]:
  assumes "fin_sat_pred F"
  obtains \<sigma> where "is_fin_sat F" "sat_pred F"
  using assms unfolding fin_sat_pred_def by auto

definition "fin_sat \<equiv> {F. fin_sat_pred F}"

lemma fin_sat_eq_Collect_fin_sat_pred [simp]: "fin_sat = {F. fin_sat_pred F}"
  unfolding fin_sat_def by simp

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

lemma is_fin_sat_if_ne_zero_if_is_n_sat:
  assumes "is_n_sat n F"
  and "n \<noteq> 0"
  shows "is_fin_sat F"
  using assms finite_if_ne_zero_is_n_clause by (intro is_fin_satI) auto

lemma finite_if_mem_if_ne_zero_if_is_n_clause:
  assumes "is_n_sat n F"
  and "n \<noteq> 0"
  and "cls \<in> set F"
  shows "finite cls"
  using assms finite_if_ne_zero_is_n_clause by auto

definition "three_sat_pred F \<equiv> is_n_sat 3 F \<and> sat_pred F"

lemma three_sat_predI [intro]:
  assumes "is_n_sat 3 F"
  and "sat_pred F"
  shows "three_sat_pred F"
  using assms unfolding three_sat_pred_def by auto

lemma three_sat_predE [elim]:
  assumes "three_sat_pred F"
  obtains "is_n_sat 3 F" "sat_pred F"
  using assms unfolding three_sat_pred_def by auto

definition "three_sat \<equiv> {F. three_sat_pred F}"

lemma three_sat_eq_Collect_three_sat_pred [simp]: "three_sat = {F. three_sat_pred F}"
  unfolding three_sat_def by simp

definition "at_most_n_clause n C \<equiv> card C \<le> n"

lemma at_most_n_clause_iff [iff]: "at_most_n_clause n C \<longleftrightarrow> card C \<le> n"
  unfolding at_most_n_clause_def by simp

definition "at_most_n_sat n F \<equiv> \<forall>cls \<in> set F. at_most_n_clause n cls"

lemma at_most_n_satI [intro]:
  assumes "\<And>cls. cls \<in> set F \<Longrightarrow> at_most_n_clause n cls"
  shows "at_most_n_sat n F"
  using assms unfolding at_most_n_sat_def by auto

lemma at_most_n_satE [elim]:
  assumes "at_most_n_sat n F"
  obtains "\<And>cls. cls \<in> set F \<Longrightarrow> at_most_n_clause n cls"
  using assms unfolding at_most_n_sat_def by auto

definition "at_most_three_sat_pred F \<equiv> at_most_n_sat 3 F \<and> sat_pred F"

lemma at_most_three_sat_predI [intro]:
  assumes "at_most_n_sat 3 F"
  and "sat_pred F"
  shows "at_most_three_sat_pred F"
  using assms unfolding at_most_three_sat_pred_def by auto

lemma at_most_three_sat_predE [elim]:
  assumes "at_most_three_sat_pred F"
  obtains "at_most_n_sat 3 F" "sat_pred F"
  using assms unfolding at_most_three_sat_pred_def by auto

end
