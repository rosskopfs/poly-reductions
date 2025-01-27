\<^marker>\<open>creator "Nico Lintner"\<close>
\<^marker>\<open>contributor "Kevin Kappelmann"\<close>
theory IS_Definition_List
  imports IS_Definition SAT_List_Definition
begin

subsection \<open>List Representation of Independent Set\<close>

type_synonym 'a ugraph_list = "'a list list"

text \<open>Translation between list and set representations.\<close>

lemma eq_set_image_set_if_Set_List_rel_Set_List_rel_eq:
  assumes "Set_List_rel Set_List_rel_eq S L"
  shows "S = set ` set L"
  using assms by (auto dest: Set_List_relD rel_setD2 simp: rel_set_eq iff: image_iff)
  (meson eq_set_if_Set_List_rel_eq rel_set_def)

corollary Set_List_rel_Set_List_rel_eq_transl_set_set_list_list_self:
  assumes "Set_List_rel Set_List_rel_eq S L"
  obtains "finite S" "\<And>s. s \<in> S \<Longrightarrow> finite s"
  using assms eq_set_image_set_if_Set_List_rel_Set_List_rel_eq by fastforce

definition "transl_list_list_set_set \<equiv> \<lambda>xs. set (transl_list_list_list_set xs)"

lemma Set_List_rel_Set_List_rel_eq_transl_list_list_set_set_self:
  "Set_List_rel Set_List_rel_eq (transl_list_list_set_set xs) xs"
  unfolding transl_list_list_set_set_def transl_list_list_list_set_eq_map_set
  by (auto simp: rel_set_def)

definition "transl_set_set_list_list \<equiv> \<lambda>S. (SOME L. transl_list_list_set_set L = S)"

lemma transl_list_list_set_set_transl_set_set_list_list_eq_self_iff_all_finite:
  "transl_list_list_set_set (transl_set_set_list_list S) = S \<longleftrightarrow> finite S \<and> (\<forall>s \<in> S. finite s)"
proof (intro iffI, goal_cases)
  case 1
  then obtain L where "set ` set L = S"
    unfolding transl_list_list_set_set_def transl_list_list_list_set_eq_map_set by auto
  then show ?case by blast
next
  case 2
  then obtain L where "set L = S" using finite_list by auto
  with 2 have "\<exists>L'. set ` set L' = S" by (metis finite_list ex_map_conv list.set_map)
  from someI_ex[OF this] show ?case by (simp add:
    transl_list_list_set_set_def  transl_set_set_list_list_def transl_list_list_list_set_eq_map_set)
qed

corollary Set_List_rel_Set_List_rel_eq_transl_set_set_list_list_selfI:
  assumes "finite S"
  and "\<And>s. s \<in> S \<Longrightarrow> finite s"
  shows "Set_List_rel Set_List_rel_eq S (transl_set_set_list_list S)"
  using assms transl_list_list_set_set_transl_set_set_list_list_eq_self_iff_all_finite
    Set_List_rel_Set_List_rel_eq_transl_list_list_set_set_self
  by metis

definition "ugraph_list E \<equiv> \<forall>e \<in> set E. list_card e = 2"

lemma ugraph_listI [intro]:
  assumes "\<And>e. e \<in> set E \<Longrightarrow> list_card e = 2"
  shows "ugraph_list E"
  using assms unfolding ugraph_list_def by simp

lemma ugraph_listE [elim]:
  assumes "ugraph_list E"
  obtains "\<And>e. e \<in> set E \<Longrightarrow> list_card e = 2"
  using assms unfolding ugraph_list_def by simp

lemma rel_fun_ugraph_ugraph_list [transfer_rule]:
  "(Set_List_rel Set_List_rel_eq ===> (=)) ugraph ugraph_list"
proof -
  have [transfer_rule]: "((Set_List_rel_eq ===> (=)) ===> Set_List_rel Set_List_rel_eq ===> (=))
    (\<lambda>p s. finite s \<and> Ball s p) list_all"
  proof (intro rel_funI)
    fix x :: "'b set \<Rightarrow> bool" and y :: "'b list \<Rightarrow> bool" and S :: "'b set set" and L :: "'b list list"
    assume [transfer_rule]: "(Set_List_rel_eq ===> (\<longleftrightarrow>)) x y" "Set_List_rel Set_List_rel_eq S L"
    then have "finite S" using Set_List_rel_Set_List_rel_eq_transl_set_set_list_list_self by auto
    then show "(finite S \<and> Ball S x) = list_all y L" unfolding list_all_iff by transfer blast
  qed
  show ?thesis unfolding ugraph_def ugraph_list_def list_all_iff[symmetric] by transfer_prover
qed

definition "list_member_list xs xss \<equiv> \<exists>ys \<in> set xss. set xs = set ys"

lemma rel_fun_mem_list_member_list [transfer_rule]:
  "(Set_List_rel_eq ===> Set_List_rel Set_List_rel_eq ===> (=)) (\<in>) list_member_list"
  unfolding list_member_list_def by (fastforce simp: rel_set_eq dest: rel_setD1 rel_setD2)

definition "is_independent_set_list E V \<equiv> \<forall>u \<in> set V. \<forall>v \<in> set V. \<not>(list_member_list [u, v] E)"

lemma is_independent_set_list_rel[transfer_rule]:
  "(Set_List_rel Set_List_rel_eq ===> Set_List_rel_eq ===> (=)) is_independent_set is_independent_set_list"
  unfolding is_independent_set_def is_independent_set_list_def by transfer_prover

definition "independent_set_pred_list E k \<equiv>
  ugraph_list E \<and> (\<exists>V \<in> set (subseqs (concat E)). list_card V \<ge> k \<and> is_independent_set_list E V)"

lemma rel_fun_independent_set_pred_independent_set_pred_list [transfer_rule]:
  "(Set_List_rel Set_List_rel_eq ===> (=) ===> (=)) independent_set_pred independent_set_pred_list"
  unfolding independent_set_pred_def independent_set_pred_list_def by transfer_prover

definition "independent_set_list \<equiv> {(E, k). independent_set_pred_list E k}"

lemma independent_set_pred_le_Domainp_Set_List_rel_Set_List_rel_eq:
  "(\<lambda>E. independent_set_pred E k) \<le> Domainp (Set_List_rel Set_List_rel_eq)"
  apply (intro predicate1I DomainPI, rule Set_List_rel_Set_List_rel_eq_transl_set_set_list_list_selfI)
  by auto (metis card_eq_0_iff independent_set_predE nat.simps numeral_2_eq_2 ugraphE)

lemma independent_set_pred_list_le_Rangep_Set_List_rel_Set_List_rel_eq:
  "(\<lambda>E. independent_set_pred_list E k) \<le> Rangep (Set_List_rel Set_List_rel_eq)"
  using Set_List_rel_Set_List_rel_eq_transl_list_list_set_set_self by fastforce

lemma rel_set_independent_set_independent_set_list [transfer_rule]:
  "rel_set (rel_prod (Set_List_rel Set_List_rel_eq) (=)) independent_set independent_set_list"
  unfolding independent_set_def independent_set_list_def
  apply (intro rel_set_Collect_Collect_if_rel_fun_if_le_Rangep_if_le_Domainp
    case_prod_le_DomainpI independent_set_pred_le_Domainp_Set_List_rel_Set_List_rel_eq
    case_prod_le_RangepI independent_set_pred_list_le_Rangep_Set_List_rel_Set_List_rel_eq)
  by auto transfer_prover

end
