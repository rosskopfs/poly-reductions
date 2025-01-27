\<^marker>\<open>creator "Nico Lintner"\<close>
\<^marker>\<open>contributor "Kevin Kappelmann"\<close>
theory SAT_List_Definition
  imports
    SAT_Definition
    Set_List_Transfer
begin

subsection \<open>List Representation of SAT\<close>

type_synonym 'a sat_list = "'a lit list list"

paragraph \<open>SAT Definitions\<close>

definition "models_clause_list \<sigma> cls \<equiv> \<exists>l \<in> set cls. (\<sigma>\<up>) l"

lemma models_clause_listI [intro]:
  assumes "l \<in> set cls"
  and "(\<sigma>\<up>) l"
  shows "models_clause_list \<sigma> cls"
  using assms unfolding models_clause_list_def by auto

lemma models_clause_listE [elim]:
  assumes "models_clause_list \<sigma> cls"
  obtains l where "l \<in> set cls" "(\<sigma>\<up>) l"
  using assms unfolding models_clause_list_def by auto

lemma rel_fun_models_clause_models_clause_list [transfer_rule]:
  "((=) ===> Set_List_rel_eq ===> (\<longleftrightarrow>)) models_clause models_clause_list"
  unfolding models_clause_def models_clause_list_def by transfer_prover

definition models_list :: "('a \<Rightarrow> bool) \<Rightarrow> 'a sat_list \<Rightarrow> bool"  where
  "models_list \<sigma> F \<equiv> \<forall>cls \<in> set F. models_clause_list \<sigma> cls"

lemma models_list_iff_ball_models_clause:
  "models_list \<sigma> F \<longleftrightarrow> (\<forall>cls \<in> set F. models_clause_list \<sigma> cls)"
  unfolding models_list_def by simp

lemma rel_fun_models_models_list [transfer_rule]:
  "((=) ===> (list_all2 Set_List_rel_eq) ===> (\<longleftrightarrow>)) models models_list"
  unfolding models_def models_list_iff_ball_models_clause by transfer_prover

definition "sat_list_pred F \<equiv> \<exists>\<sigma>. models_list \<sigma> F"

lemma sat_list_predI [intro]:
  assumes "models_list \<sigma> F"
  shows "sat_list_pred F"
  using assms unfolding sat_list_pred_def by auto

lemma sat_list_predE [elim]:
  assumes "sat_list_pred F"
  obtains \<sigma> where "models_list \<sigma> F"
  using assms unfolding sat_list_pred_def by auto

lemma rel_fun_sat_pred_sat_list_pred [transfer_rule]:
  "(list_all2 Set_List_rel_eq ===> (=)) sat_pred sat_list_pred"
  unfolding sat_pred_def sat_list_pred_def by transfer_prover

lemma rel_fun_fin_sat_pred_sat_list_pred [transfer_rule]:
  "(list_all2 Set_List_rel_eq ===> (=)) fin_sat_pred sat_list_pred"
proof (intro rel_funI)
  fix F :: " 'a lit set list" and G assume [transfer_rule]: "list_all2 Set_List_rel_eq F G"
  then have eq: "fin_sat_pred F = sat_pred F"
    by (auto dest: finite_if_mem_if_list_all2_Set_List_rel_eq)
  show "fin_sat_pred F = sat_list_pred G" by (subst eq) transfer_prover
qed

definition "sat_list \<equiv> {F. sat_list_pred F}"

lemma sat_list_eq_Collect_sat_list_pred [simp]: "sat_list = {F. sat_list_pred F}"
  unfolding sat_list_def by simp

lemma rel_set_Collect_Collect_if_rel_fun_if_le_Rangep_if_le_Domainp:
  assumes "P \<le> Domainp R"
  assumes "Q \<le> Rangep R"
  and "(R ===> (\<longleftrightarrow>)) P Q"
  shows "rel_set R (Collect P) (Collect Q)"
  using assms by (intro rel_setI) (fastforce dest: rel_funD)+

lemma case_prod_le_DomainpI:
  assumes "\<And>y. (\<lambda>x. T x y) \<le> Domainp R"
  and "\<And>x. (T x) \<le> Domainp S"
  shows "(\<lambda>(x, y). T x y) \<le> Domainp (rel_prod R S)"
proof (intro predicate1I)
  fix p presume "(\<lambda>(x, y). T x y) p"
  moreover then obtain x y where p_eq: "p = (x, y)" by auto
  ultimately obtain x' y' where "R x x'" "S y y'" using assms by force
  with p_eq show "Domainp (rel_prod R S) p" by (intro DomainPI[where b="(x', y')"]) auto
qed

lemma case_prod_le_RangepI:
  assumes "\<And>y. (\<lambda>x. T x y) \<le> Rangep R"
  and "\<And>x. (T x) \<le> Rangep S"
  shows "(\<lambda>(x, y). T x y) \<le> Rangep (rel_prod R S)"
proof (intro predicate1I)
  fix p presume "(\<lambda>(x, y). T x y) p"
  moreover then obtain x y where p_eq: "p = (x, y)" by auto
  ultimately obtain x' y' where "R x' x" "S y' y" using assms by force
  with p_eq show "Rangep (rel_prod R S) p" by (intro RangePI[where a="(x', y')"]) auto
qed

lemma fin_sat_list_pred_le_Domainp_list_all2_Set_List_rel_eq:
  "fin_sat_pred \<le> Domainp (list_all2 Set_List_rel_eq)"
  by (intro predicate1I DomainPI, rule list_all2_Set_List_rel_transl_set_list_list_listI)
  (auto intro: finite_if_mem_if_ne_zero_if_is_n_clause)

lemma sat_list_pred_le_Rangep_list_all2_Set_List_rel_eq:
  "sat_list_pred \<le> Rangep (list_all2 Set_List_rel_eq)"
  by (meson RangePI list_all2_Set_List_rel_transl_list_list_list_set predicate1I)

lemma rel_set_fin_sat_sat_list [transfer_rule]:
  "rel_set (list_all2 Set_List_rel_eq) fin_sat sat_list"
  unfolding fin_sat_def sat_list_def
  using fin_sat_list_pred_le_Domainp_list_all2_Set_List_rel_eq
    sat_list_pred_le_Rangep_list_all2_Set_List_rel_eq
    rel_fun_fin_sat_pred_sat_list_pred
  by (intro rel_set_Collect_Collect_if_rel_fun_if_le_Rangep_if_le_Domainp)

definition "list_card xs = card (set xs)"

lemma list_card_eq_card_set: "list_card xs = card (set xs)"
  unfolding list_card_def by simp

lemma rel_fun_card_list_card [transfer_rule]:
  "(Set_List_rel_eq ===> (=)) card list_card"
  unfolding list_card_eq_card_set by (fastforce simp: rel_set_eq)

definition "is_n_clause_list n C \<equiv> is_n_clause n (set C)"

lemma is_n_clause_list_iff_is_n_clause_set: "is_n_clause_list n C \<longleftrightarrow> is_n_clause n (set C)"
  unfolding is_n_clause_list_def by simp

lemma is_n_clause_list_iff_list_card_eq: "is_n_clause_list n C \<longleftrightarrow> list_card C = n"
  by (simp add: is_n_clause_list_iff_is_n_clause_set list_card_eq_card_set)

lemma rel_fun_is_n_clause_is_n_clause_list [transfer_rule]:
  "((=) ===> Set_List_rel_eq ===> (\<longleftrightarrow>)) is_n_clause is_n_clause_list"
  unfolding is_n_clause_list_iff_list_card_eq is_n_clause_def
  by transfer_prover

definition "is_n_sat_list n F \<equiv> \<forall>cls \<in> set F. is_n_clause_list n cls"

lemma is_n_sat_listI [intro]:
  assumes "\<And>cls. cls \<in> set F \<Longrightarrow> is_n_clause_list n cls"
  shows "is_n_sat_list n F"
  using assms unfolding is_n_sat_list_def by auto

lemma is_n_sat_listE [elim]:
  assumes "is_n_sat_list n F"
  obtains "\<And>cls. cls \<in> set F \<Longrightarrow> is_n_clause_list n cls"
  using assms unfolding is_n_sat_list_def by auto

lemma rel_fun_is_n_sat_is_n_sat_list [transfer_rule]:
  "((=) ===> list_all2 Set_List_rel_eq ===> (\<longleftrightarrow>)) is_n_sat is_n_sat_list"
  unfolding is_n_sat_def is_n_sat_list_def by transfer_prover

definition "three_sat_list_pred F \<equiv> is_n_sat_list 3 F \<and> sat_list_pred F"

lemma three_sat_list_predI [intro]:
  assumes "is_n_sat_list 3 F"
  and "sat_list_pred F"
  shows "three_sat_list_pred F"
  using assms unfolding three_sat_list_pred_def by auto

lemma three_sat_list_predE [elim]:
  assumes "three_sat_list_pred F"
  obtains "is_n_sat_list 3 F" "sat_list_pred F"
  using assms unfolding three_sat_list_pred_def by auto

lemma rel_fun_three_sat_pred_three_sat_list_pred [transfer_rule]:
  "(list_all2 Set_List_rel_eq ===> (\<longleftrightarrow>)) three_sat_pred three_sat_list_pred"
  unfolding three_sat_pred_def three_sat_list_pred_def
  by transfer_prover

definition "three_sat_list \<equiv> {F. three_sat_list_pred F}"

lemma three_sat_list_eq_Collect_three_sat_list_pred [simp]:
  "three_sat_list = {F. three_sat_list_pred F}"
  unfolding three_sat_list_def by simp

lemma three_sat_list_pred_le_Domainp_list_all2_Set_List_rel_eq:
  "three_sat_pred \<le> Domainp (list_all2 Set_List_rel_eq)"
  by (intro predicate1I DomainPI, rule list_all2_Set_List_rel_transl_set_list_list_listI)
  (auto intro: finite_if_mem_if_ne_zero_if_is_n_clause)

lemma three_sat_list_pred_le_Rangep_list_all2_Set_List_rel_eq:
  "three_sat_list_pred \<le> Rangep (list_all2 Set_List_rel_eq)"
  by (meson RangePI list_all2_Set_List_rel_transl_list_list_list_set predicate1I)

lemma rel_set_three_sat_three_sat_list [transfer_rule]:
  "rel_set (list_all2 Set_List_rel_eq) three_sat three_sat_list"
  unfolding three_sat_def three_sat_list_def

  using three_sat_list_pred_le_Domainp_list_all2_Set_List_rel_eq
    three_sat_list_pred_le_Rangep_list_all2_Set_List_rel_eq
    rel_fun_three_sat_pred_three_sat_list_pred
  by (intro rel_set_Collect_Collect_if_rel_fun_if_le_Rangep_if_le_Domainp)

definition "at_most_n_clause_list n C \<equiv> at_most_n_clause n (set C)"

lemma at_most_n_clause_list_iff_at_most_n_clause_set:
  "at_most_n_clause_list n C \<longleftrightarrow> at_most_n_clause n (set C)"
  unfolding at_most_n_clause_list_def by simp

lemma at_most_n_clause_list_iff_le_list_card: "at_most_n_clause_list n C \<longleftrightarrow> list_card C \<le> n"
  by (simp add: at_most_n_clause_list_iff_at_most_n_clause_set list_card_eq_card_set)

lemma rel_fun_at_most_n_clause_at_most_n_clause_list [transfer_rule]:
  "((=) ===> Set_List_rel_eq ===> (\<longleftrightarrow>)) at_most_n_clause at_most_n_clause_list"
  unfolding at_most_n_clause_list_iff_le_list_card at_most_n_clause_def
  by transfer_prover

definition "at_most_n_sat_list n F \<equiv> \<forall>cls \<in> set F. at_most_n_clause_list n cls"

lemma at_most_n_sat_listI [intro]:
  assumes "\<And>cls. cls \<in> set F \<Longrightarrow> at_most_n_clause_list n cls"
  shows "at_most_n_sat_list n F"
  using assms unfolding at_most_n_sat_list_def by auto

lemma at_most_n_sat_listE [elim]:
  assumes "at_most_n_sat_list n F"
  obtains "\<And>cls. cls \<in> set F \<Longrightarrow> at_most_n_clause_list n cls"
  using assms unfolding at_most_n_sat_list_def by auto

lemma rel_fun_at_most_n_sat_at_most_n_sat_list [transfer_rule]:
  "((=) ===> list_all2 Set_List_rel_eq ===> (\<longleftrightarrow>)) at_most_n_sat at_most_n_sat_list"
  unfolding at_most_n_sat_def at_most_n_sat_list_def by transfer_prover

definition "at_most_three_sat_list_pred F \<equiv> at_most_n_sat_list 3 F \<and> sat_list_pred F"

lemma at_most_three_sat_list_predI [intro]:
  assumes "at_most_n_sat_list 3 F"
  and "sat_list_pred F"
  shows "at_most_three_sat_list_pred F"
  using assms unfolding at_most_three_sat_list_pred_def by auto

lemma at_most_three_sat_list_predE [elim]:
  assumes "at_most_three_sat_list_pred F"
  obtains "at_most_n_sat_list 3 F" "sat_list_pred F"
  using assms unfolding at_most_three_sat_list_pred_def by auto

lemma rel_fun_at_most_three_sat_pred_at_most_three_sat_list_pred [transfer_rule]:
  "(list_all2 Set_List_rel_eq ===> (\<longleftrightarrow>)) at_most_three_sat_pred at_most_three_sat_list_pred"
  unfolding at_most_three_sat_pred_def at_most_three_sat_list_pred_def
  by transfer_prover

definition "at_most_three_sat_list \<equiv> {F. at_most_three_sat_list_pred F}"

lemma at_most_three_sat_list_eq_Collect_at_most_three_sat_list_pred [simp]:
  "at_most_three_sat_list = {F. at_most_three_sat_list_pred F}"
  unfolding at_most_three_sat_list_def by simp

end
