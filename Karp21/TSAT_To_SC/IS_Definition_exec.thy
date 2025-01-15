theory IS_Definition_exec
  imports IS_Definition Poly_Reductions_Lib.SAT_Definition_exec
begin

subsection \<open>list representation of Independent Set\<close>

definition
  "ugraph_exec \<equiv> list_all (\<lambda>xs. length (remdups xs) = 2)"

definition
  "list_member xs \<equiv> list_ex (\<lambda>ys. set xs = set ys)"

definition
  "is_independent_set_exec E V \<equiv> list_all (\<lambda>u. list_all (\<lambda>v. \<not> list_member [u, v] E) V) V"

definition
  "independent_set_pred \<equiv> \<lambda>(E, k). ugraph E \<and> (\<exists>V \<in> Pow (\<Union> E). card V \<ge> k \<and> is_independent_set E V)"

lemma independent_set_unfold_pred: "independent_set = {E. independent_set_pred E}"
  unfolding independent_set_def independent_set_pred_def by blast

definition
  "independent_set_pred_exec \<equiv> \<lambda>(E, k). ugraph_exec E \<and> list_ex (\<lambda>V. length (remdups V) \<ge> k \<and> is_independent_set_exec E V) (subseqs (concat E))"

definition
  "independent_set_exec \<equiv> {E. independent_set_pred_exec E}"


subsection \<open>relators and relations to show that \<open>independent_set\<close> and \<open>independent_set_exec\<close> are related\<close>

definition
  "IS_List_rel \<equiv> rel_prod (Set_List_rel Set_List_rel_eq) (=)"

lemma IS_List_relI[intro]:
  assumes "S = set ` set L"
  shows "IS_List_rel (S, k) (L, k)"
  unfolding IS_List_rel_def using assms by (auto simp: rel_set_def)

lemma IS_List_relE[elim]:
  assumes "IS_List_rel (S, k1) (L, k2)"
  obtains "S = set ` set L" "k1 = k2"
  using assms unfolding IS_List_rel_def by (fastforce simp: rel_set_eq dest: rel_setD1 rel_setD2)

lemma IS_List_relD[dest!]:
  assumes "IS_List_rel (S, k) (L, k)"
  obtains "S = set ` set L"
  using assms by (rule IS_List_relE)

lemma IS_List_rel_iff[simp]: "IS_List_rel = rel_prod (Set_List_rel (Set_List_rel_eq)) (=)"
  unfolding IS_List_rel_def by simp

unbundle lifting_syntax

lemma Ball_list_all_rel[transfer_rule]: "((r ===> (=)) ===> Set_List_rel r ===> (=)) (\<lambda>p F. Ball F p) list_all"
  by (auto 0 4 simp: in_set_conv_nth list_all_length rel_set_def rel_fun_def)

lemma empty_Nil_rel[transfer_rule]: "Set_List_rel r {} []"
  by (auto simp: rel_set_def)

lemma insert_Cons_rel[transfer_rule]: "(r ===> Set_List_rel r ===> Set_List_rel r) insert Cons"
  by (fastforce simp: rel_set_def)

lemma Union_concat_rel[transfer_rule]: "(Set_List_rel (Set_List_rel r) ===> Set_List_rel r) (\<Union>) concat"
  by (fastforce simp: rel_set_def)

lemma Pow_subseqs_rel[transfer_rule]: "(Set_List_rel_eq ===> Set_List_rel (Set_List_rel_eq)) Pow subseqs"
proof (intro rel_funI Set_List_relI rel_setI, goal_cases)
  case (1 x y s)
  then have "s \<in> set ` set (subseqs y)"
    using subseqs_powset[of y] by blast
  then show ?case by blast
next
  case (2 x y l)
  then have "set l \<in> Pow x"
    using subseqs_powset[of y] by blast
  then show ?case by blast
qed


paragraph \<open>\<open>independent_set\<close> and \<open>independent_set_exec\<close> are related\<close>

lemma ugraph_exec_rel[transfer_rule]: "(Set_List_rel Set_List_rel_eq ===> (=)) ugraph ugraph_exec"
proof -
  have [transfer_rule]: "((Set_List_rel_eq ===> (=)) ===> Set_List_rel Set_List_rel_eq ===> (=)) (\<lambda>p s. finite s \<and> Ball s p) list_all"
  proof (intro rel_funI) fix x::"'b set \<Rightarrow> bool" and y::"'b list \<Rightarrow> bool" and S::"'b set set" and L::"'b list list"
    assume [transfer_rule]: "(Set_List_rel_eq ===> (=)) x y" "Set_List_rel Set_List_rel_eq S L"
    then have "S = set ` set L"
      by (fastforce dest: rel_setD1 rel_setD2)
    then have "finite S" by blast
    then show "(finite S \<and> Ball S x) = list_all y L"
      by transfer blast
  qed
  show ?thesis
    unfolding ugraph_def ugraph_exec_def by transfer_prover
qed

lemma Set_member_list_member_rel[transfer_rule]: "(Set_List_rel_eq ===> Set_List_rel Set_List_rel_eq ===> (=)) (\<in>) list_member"
  unfolding list_member_def by (fastforce simp: rel_set_eq list_ex_iff dest: rel_setD1 rel_setD2)

lemma is_independent_set_exec_rel[transfer_rule]:
    "(Set_List_rel (Set_List_rel_eq) ===> Set_List_rel_eq ===> (=)) is_independent_set is_independent_set_exec"
  unfolding is_independent_set_def is_independent_set_exec_def by transfer_prover

lemma independent_set_pred_exec_rel[transfer_rule]: "(IS_List_rel ===> (=)) independent_set_pred independent_set_pred_exec"
  unfolding independent_set_pred_def independent_set_pred_exec_def IS_List_rel_iff by transfer_prover

lemma independent_set_exec_rel: "rel_set IS_List_rel independent_set independent_set_exec"
  unfolding independent_set_def independent_set_exec_def independent_set_pred_exec_def
proof (intro rel_setI, goal_cases)
  case (1 S)
  then have ugraph: "ugraph (fst S)"
    by auto
  then have finite: "finite (fst S)" "\<forall>e \<in> (fst S). finite e"
    unfolding ugraph_def using card_gt_0_iff by fastforce+
  then have "\<exists>L'. fst S = set L'" "\<forall>e \<in> (fst S). \<exists>xs. e = set xs"
    using finite_list by fast+
  then obtain El where El_obt: "fst S = set ` set El"
    by (metis List.finite_set finite_list finite_subset_image rangeI subset_eq)
  with ugraph[unfolded ugraph_def] have fst_S_El_rel: "Set_List_rel Set_List_rel_eq (fst S) El" "Set_List_rel Set_List_rel_eq (fst S) El"
    by (auto simp: rel_set_def)
  then have "IS_List_rel S (El, snd S)"
    by (simp add: rel_prod_sel)
  moreover from this 1 have "(El, snd S) \<in> {(E, k). ugraph_exec E \<and> list_ex (\<lambda>V. length (remdups V) \<ge> k \<and> is_independent_set_exec E V) (subseqs (concat E))}"
    unfolding independent_set_def[symmetric] independent_set_unfold_pred independent_set_pred_exec_def[symmetric]
    using independent_set_pred_exec_rel by (blast dest: rel_funD)
  ultimately show ?case by blast
next
  case (2 L)
  define Es where "Es = set ` set (fst L)"
  with 2 have "\<forall>s \<in> Es. card s = 2"
    by (simp add: case_prod_beta' length_remdups_card_conv list.pred_set ugraph_exec_def )
  with Es_def have Es_fst_L_rel: "Set_List_rel Set_List_rel_eq Es (fst L)" "Set_List_rel Set_List_rel_eq Es (fst L)"
    by (auto simp: rel_set_def)
  then have "IS_List_rel (Es, snd L) (fst L, snd L)"
    by (simp add: rel_prod_sel)
  moreover from this 2 have "(Es, snd L) \<in> {(E, k). ugraph E \<and> (\<exists>V\<in>Pow (\<Union> E). k \<le> card V \<and> is_independent_set E V)}"
    unfolding independent_set_pred_def[symmetric] independent_set_pred_exec_def[symmetric]
    using independent_set_pred_exec_rel by (auto dest: rel_funD)
  ultimately show ?case by auto
qed


subsection \<open>translating between list and set representations\<close>

definition
  "transl_IS_list_set \<equiv> \<lambda>(L, k). (set ` set L, k)"

lemma transl_IS_list_set_iff[simp]: "transl_IS_list_set = (\<lambda>(L, k). (set ` set L, k))"
  unfolding transl_IS_list_set_def by simp

lemma transl_IS_list_set_rel[transfer_rule]: "IS_List_rel (transl_IS_list_set x) x"
  by (induction "fst x") (auto simp: rel_set_def split: prod.split)

lemma IS_p_exec_IS_p_transl_iff: "independent_set_pred_exec x \<longleftrightarrow> independent_set_pred (transl_IS_list_set x)"
  using transl_IS_list_set_rel independent_set_pred_exec_rel by (blast dest: rel_funD)

definition
  "transl_IS_set_list \<equiv> \<lambda>(S, k). (SOME L. set ` set L = S , k)"

lemma transl_IS_set_list_iff[simp]: "transl_IS_set_list = (\<lambda>(S, k). (SOME L. set ` set L = S , k))"
  unfolding transl_IS_set_list_def by simp

lemma transl_IS_id: "finite L \<and> (\<forall>l \<in> L. finite l) \<longleftrightarrow> transl_IS_list_set (transl_IS_set_list (L, k)) = (L, k)"
proof (intro iffI, goal_cases)
  case 1
  then obtain L' where "set L' = L"
    using finite_list by auto
  with 1 have "\<exists>L'. set ` set L' = L"
    using finite_list ex_map_conv[of L' set] unfolding list.set_map[symmetric] by metis
  from someI_ex[OF this] show ?case by simp
next
  case 2
  then have "\<exists>L'. set ` set L' = L" by auto
  then show ?case by blast
qed

lemma transl_IS_set_list_rel[transfer_rule]: "finite S \<Longrightarrow> (\<forall>s \<in> S. finite s) \<Longrightarrow> IS_List_rel (S, k) (transl_IS_set_list (S, k))"
  using transl_IS_id[of S k] transl_IS_list_set_rel[of "transl_IS_set_list (S, k)"] by presburger

lemma transl_IS_set_list_finite:
  assumes "IS_List_rel (S, k) (transl_IS_set_list (S, k))"
  shows "finite S" "\<And>s. s \<in> S \<Longrightarrow> finite s"
proof -
  have "IS_List_rel (S, k) (transl_IS_set_list (S, k)) \<Longrightarrow> \<exists>S'. set ` set S' = S"
    by (rule IS_List_relD) auto
  with assms show "finite S" "\<And>s. s \<in> S \<Longrightarrow> finite s"
    by blast+
qed

end