theory SAT_Definition_exec
  imports SAT_Definition
begin

subsection \<open>list representation of Three CNF SAT\<close>

type_synonym 'a sat_list = "'a lit list list"

definition models_exec :: "('a \<Rightarrow> bool) \<Rightarrow> 'a sat_list \<Rightarrow> bool"  where
  "models_exec \<sigma> F \<equiv> list_all (list_ex (lift \<sigma>)) F"

definition sat_exec :: "'a sat_list \<Rightarrow> bool"  where
  "sat_exec F \<equiv> \<exists>\<sigma>. models_exec \<sigma> F"

definition
  "three_cnf_sat_pred F \<equiv> sat F \<and> (\<forall>cls \<in> set F. card cls = 3)"

lemma three_cnf_sat_unfold_pred: "three_cnf_sat = {F. three_cnf_sat_pred F}"
  unfolding three_cnf_sat_def three_cnf_sat_pred_def by (rule refl)

definition
  "three_cnf_sat_pred_exec F \<equiv> sat_exec F \<and> (list_all (\<lambda>xs. length (remdups xs) = 3) F)"

definition
  "three_cnf_sat_exec \<equiv> {F. three_cnf_sat_pred_exec F}"


subsection \<open>relators and relations to show that \<open>three_cnf_sat\<close> and \<open>three_cnf_sat_exec\<close> are related\<close>

definition
  "Set_List_rel r s xs \<equiv> rel_set r s (set xs)"

lemma Set_List_relI[intro]: 
  assumes "rel_set r s (set xs)"
  shows "Set_List_rel r s xs"
  unfolding Set_List_rel_def using assms .

lemma Set_List_relD[dest]:
  assumes "Set_List_rel r s xs"
  shows "rel_set r s (set xs)" 
  using assms unfolding Set_List_rel_def .

lemma Set_List_rel_iff[simp]: "Set_List_rel r s xs \<longleftrightarrow> rel_set r s (set xs)"
  by blast

abbreviation
  "Set_List_rel_eq \<equiv> Set_List_rel (=)"
lemmas Set_List_rel_eqI[intro] = Set_List_relI[where r="(=)", unfolded rel_set_eq]
lemmas Set_List_rel_eqD[dest] = Set_List_relD[where r="(=)", unfolded rel_set_eq]

unbundle lifting_syntax

lemma Ball_set_list_all_rel[transfer_rule]: "((r ===> (=)) ===> list_all2 r ===> (=)) (\<lambda>p F. Ball (set F) p) list_all"
  by (fastforce simp: in_set_conv_nth list_all2_conv_all_nth list_all_length dest: rel_funD)

lemma Bex_list_ex_rel[transfer_rule]: "((r ===> (=)) ===> Set_List_rel r ===> (=)) (\<lambda>p s. Bex s p) list_ex"
proof (intro rel_funI) fix x::"'a \<Rightarrow> bool" and y xs ys
  show "(r ===> (=)) x y \<Longrightarrow> Set_List_rel r xs ys \<Longrightarrow> Bex xs x = list_ex y ys"
    using Bex_set_list_ex[of ys y] by (fastforce simp: rel_set_def rel_fun_def)
qed

lemma id_remdups_rel[transfer_rule]: "(Set_List_rel r ===> (\<lambda>s xs. Set_List_rel r s xs \<and> distinct xs)) (\<lambda>s. s) remdups"
  by auto

lemma card_len_rel[transfer_rule]: "((\<lambda>s xs. Set_List_rel_eq s xs \<and> distinct xs) ===> (=)) card length"
  by (auto simp: length_remdups_card_conv rel_set_eq distinct_card)


paragraph \<open>\<open>three_cnf_sat\<close> and \<open>three_cnf_sat_exec\<close> are related\<close>

lemma models_exec_rel[transfer_rule]: "((=) ===> (list_all2 Set_List_rel_eq) ===> (=)) models models_exec"
  unfolding models_def models_exec_def by transfer_prover

lemma sat_exec_rel[transfer_rule]: "(list_all2 Set_List_rel_eq ===> (=)) sat sat_exec"
  unfolding sat_def sat_exec_def by transfer_prover

lemma three_cnf_sat_pred_exec_rel[transfer_rule]:
    "(list_all2 Set_List_rel_eq ===> (=)) three_cnf_sat_pred three_cnf_sat_pred_exec"
  unfolding three_cnf_sat_pred_def three_cnf_sat_pred_exec_def by transfer_prover

lemma three_cnf_sat_exec_rel:
    "rel_set (list_all2 Set_List_rel_eq) three_cnf_sat three_cnf_sat_exec"
proof -
  have all_card_n_list_rel: "(list_all2 Set_List_rel_eq ===> (=)) (\<lambda>F. \<forall>cls\<in>set F. card cls = n) (\<lambda>F. list_all (\<lambda>xs. length (remdups xs) = n) F)" for n
    by transfer_prover
  show ?thesis
    unfolding three_cnf_sat_def three_cnf_sat_exec_def[unfolded three_cnf_sat_pred_exec_def]
  proof (intro rel_setI, goal_cases)
    case (1 Fs)
    then have "\<forall>s \<in> set Fs. finite s"
      using card_eq_0_iff by fastforce
    then have "\<forall>s \<in> set Fs. \<exists>xs. s = set xs"
      using finite_list by fast
    then obtain Fl where "list_all2 Set_List_rel_eq Fs Fl"
      by (induction Fs) (fastforce simp: rel_set_eq)+
    with 1 show ?case
      using sat_exec_rel all_card_n_list_rel by (blast dest: rel_funD)
  next
    case (2 Fl)
    then have "\<forall>xs \<in> set Fl. \<exists>s. s = set xs"
      by simp
    then obtain Fs where obt: "list_all2 Set_List_rel_eq Fs Fl"
      by (induction Fl) (fastforce simp: rel_set_eq)+
    with 2 show ?case
      using sat_exec_rel all_card_n_list_rel by (blast dest: rel_funD)
  qed
qed


subsection \<open>translating between list and set representations\<close>

definition
  "transl_SAT_list_set \<equiv> map set"

lemma transl_sat_list_set_iff[simp]: "transl_SAT_list_set = map set"
  unfolding transl_SAT_list_set_def by simp

lemma transl_SAT_list_set_rel[transfer_rule]: "list_all2 Set_List_rel_eq (transl_SAT_list_set L) L"
  by (induction L) (simp_all add: rel_set_eq)

lemma TSAT_p_exec_TSAT_p_transl_iff: "three_cnf_sat_pred_exec F \<longleftrightarrow> three_cnf_sat_pred (transl_SAT_list_set F)"
  using transl_SAT_list_set_rel three_cnf_sat_pred_exec_rel by (blast dest: rel_funD)

definition
  "transl_SAT_set_list \<equiv> map (\<lambda>s. (SOME xs. set xs = s))"

lemma transl_SAT_set_list_iff[simp]: "transl_SAT_set_list = map (\<lambda>s. (SOME xs. set xs = s))"
  unfolding transl_SAT_set_list_def by simp

lemma transl_SAT_id: "list_all finite F \<longleftrightarrow> transl_SAT_list_set (transl_SAT_set_list F) = F"
proof (induction F)
  case (Cons f F)
  show ?case
  proof (cases "finite f")
    case True
    then have "set (SOME xs. set xs = f) = f"
      using finite_list someI_ex[of "\<lambda>xs. set xs = f"] by blast
    with Cons True show ?thesis by simp
  next
    case False
    then have "(transl_SAT_list_set (transl_SAT_set_list (f # F)) = f # F) \<Longrightarrow> False"
      by (metis Cons_eq_map_conv List.finite_set transl_sat_list_set_iff)
    with False show ?thesis by auto
  qed
qed simp

lemma transl_SAT_set_list_rel[transfer_rule]: "list_all finite F \<Longrightarrow> list_all2 Set_List_rel_eq F (transl_SAT_set_list F)"
  using transl_SAT_id[of F] transl_SAT_list_set_rel[of "transl_SAT_set_list F"] by presburger

lemma transl_SAT_set_list_finite:
  assumes "list_all2 Set_List_rel_eq F (transl_SAT_set_list F)"
  shows "\<And>f. f \<in> set F \<Longrightarrow> finite f"
proof - fix f::"'a set"
  assume "f \<in> set F"
  with assms have "f = set (SOME xs. set xs = f)"
    by (auto simp: rel_set_eq in_set_conv_nth list_all2_conv_all_nth)
  then show "finite f"
    using finite_set[of "SOME xs. set xs = f"] by argo
qed

end