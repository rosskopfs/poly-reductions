\<^marker>\<open>creator "Nico Lintner"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Set_List_Transfer
  imports Main
begin

unbundle lifting_syntax

text \<open>Relators and transports between sets and lists.\<close>

definition "Set_List_rel R s xs \<equiv> rel_set R s (set xs)"

lemma Set_List_relI:
  assumes "rel_set R s (set xs)"
  shows "Set_List_rel R s xs"
  unfolding Set_List_rel_def using assms .

lemma Set_List_relD:
  assumes "Set_List_rel R s xs"
  shows "rel_set R s (set xs)"
  using assms unfolding Set_List_rel_def .

lemma Set_List_rel_iff [iff]: "Set_List_rel R s xs \<longleftrightarrow> rel_set R s (set xs)"
  using Set_List_relI Set_List_relD by blast

lemma right_total_Set_List_rel[transfer_rule]:
  "right_total R \<Longrightarrow> right_total (Set_List_rel R)"
  unfolding Set_List_rel_def
  by (metis right_total_def right_total_rel_set)

lemma left_unique_Set_List_rel[transfer_rule]:
  "left_unique R \<Longrightarrow> left_unique (Set_List_rel R)"
  by (metis Set_List_rel_def left_unique_def left_unique_rel_set)

lemma Set_List_rel_setI:
  assumes "list_all2 R xs ys"
  shows "Set_List_rel R (set xs) ys"
  using assms unfolding Set_List_rel_def
  by (meson list.set_transfer rel_funE)

abbreviation "Set_List_rel_eq \<equiv> Set_List_rel (=)"

lemma Domainp_Set_List_rel_eq[relator_domain]:
  assumes "left_unique R"
  shows "Domainp (Set_List_rel R) = (\<lambda>A. finite A \<and> Ball A (Domainp R))"
proof -
  have [simp]: "finite X" if "rel_set R X (set xs)" for X xs
  proof -
    from assms that have "X = {(THE x'. R x' x) | x. x \<in> set xs}"
      unfolding left_unique_def rel_set_def
      by auto (metis the_equality)+
    then show ?thesis
      by simp
  qed
  have "Ex (Set_List_rel R X)" if "finite X" "\<forall>x \<in> X. \<exists>x'. R x x'" for X
  proof -
    from that obtain xs where "set xs = X"
      using finite_list by blast
    moreover from this that have "\<exists>ys. list_all2 R xs ys"
      by (induction xs arbitrary: X) fastforce+
    ultimately show ?thesis
      using Set_List_rel_setI by blast
  qed
  with assms show ?thesis
    unfolding Domainp_iff
    by (intro ext) (fastforce simp: rel_set_def)
qed

lemma Domain_Set_List_rel_eq_eq_finite[transfer_domain_rule]:
  "Domainp Set_List_rel_eq = finite"
  unfolding Set_List_rel_def rel_set_def Domainp_iff
  apply(intro ext)
  by (metis List.finite_set finite_distinct_list set_eqI)


lemma eq_set_if_Set_List_rel_eq:
  assumes "Set_List_rel_eq s xs"
  shows "s = set xs"
  using assms by (simp add: rel_set_eq)

lemma finite_if_Set_List_rel_eq:
  assumes "Set_List_rel_eq s xs"
  shows "finite s"
  using assms eq_set_if_Set_List_rel_eq by auto

lemma Set_List_nil [transfer_rule]: "Set_List_rel R {} []"
  by (auto simp: rel_set_def)

lemma Set_List_rel_Cons [transfer_rule]: "(R ===> Set_List_rel R ===> Set_List_rel R) insert Cons"
  by (fastforce simp: rel_set_def)

lemma rel_fun_Set_List_rel_id_set [transfer_rule]: "(Set_List_rel R ===> rel_set R) (\<lambda>x. x) set"
  by blast

lemma rel_fun_enumerate [transfer_rule]:
  "((=) ===> list_all2 (Set_List_rel R) ===> list_all2 (rel_prod (=) (Set_List_rel R)))
  enumerate enumerate"
  by (fastforce simp: list_all2_conv_all_nth nth_enumerate_eq)

lemma rel_fun_image_map [transfer_rule]:
  "((R ===> S) ===> Set_List_rel R ===> Set_List_rel S) image map"
  by (fastforce simp: rel_set_def dest: rel_funD)

lemma rel_fun_Times_product [transfer_rule]:
  "(Set_List_rel R ===> Set_List_rel S ===> Set_List_rel (rel_prod R S)) (\<times>) List.product"
  by (fastforce simp: rel_set_def dest: rel_funD)

lemma rel_fun_union_concat [transfer_rule]:
  "(Set_List_rel (Set_List_rel R) ===> Set_List_rel R) (\<Union>) concat"
  by (fastforce simp: rel_set_def)

lemma rel_fun_Union_set_concat [transfer_rule]:
  "(list_all2 (Set_List_rel R) ===> (Set_List_rel R)) (\<lambda>s. \<Union>(set s)) concat"
  by (fastforce simp: in_set_conv_nth list_all2_conv_all_nth rel_set_def)

lemma rel_fun_set_filter_list_filter [transfer_rule]:
  "((R ===> (\<longleftrightarrow>)) ===> Set_List_rel R ===> Set_List_rel R) Set.filter filter"
  by (fastforce simp: rel_set_def dest: rel_funD)

lemma rel_fun_set_filter_list_filter_pred:
  assumes "(R ===> (\<longleftrightarrow>)) p p'"
  shows "(Set_List_rel R ===> Set_List_rel (\<lambda>a b. R a b \<and> p a)) (Set.filter p) (filter p')"
  using assms by (fastforce simp: rel_set_def dest: rel_funD)

lemma rel_fun_union_append [transfer_rule]:
  "(Set_List_rel R ===> Set_List_rel R ===> Set_List_rel R) (\<union>) (@)"
  by (fastforce simp: rel_set_def)

lemma rel_fun_Ball_set_list_all [transfer_rule]:
  "((R ===> (=)) ===> list_all2 R ===> (=)) (\<lambda>p F. Ball (set F) p) list_all"
  by (fastforce simp: in_set_conv_nth list_all2_conv_all_nth list_all_length dest: rel_funD)

lemma rel_fun_mem_list_member [transfer_rule]:
  assumes "bi_unique R"
  shows "(Set_List_rel R ===> R ===> (\<longleftrightarrow>)) (\<lambda>S x. x \<in> S) List.member"
  using assms unfolding list.set_intros
  by (intro rel_funI) (auto simp: rel_set_def dest: bi_uniqueDr bi_uniqueDl)

lemma filter_mem_subseqs: "filter P xs \<in> set (subseqs xs)"
  apply (induction xs) by auto[]
  (metis (no_types, lifting) UnCI filter.simps(2) image_eqI list.set_map set_append subseqs.simps(2))

lemma rel_fun_Pow_subseqs [transfer_rule]:
  "(Set_List_rel R ===> Set_List_rel (Set_List_rel R)) Pow subseqs"
proof (intro rel_funI Set_List_relI rel_setI, goal_cases)
  case (1 X xs X')
  let ?xs' = "filter (\<lambda>x. \<exists>y \<in> X'. R y x) xs"
  from 1 have "Set_List_rel R X' ?xs'" unfolding rel_set_def Set_List_rel_iff by force
  with filter_mem_subseqs show ?case by blast
next
  case (2 X xs xs')
  let ?X' = "{x \<in> X. \<exists>y \<in> set xs'. R x y}"
  from 2 have "Set_List_rel R ?X' xs'" unfolding rel_set_def Set_List_rel_iff
    by auto (metis Pow_iff image_iff in_mono subseqs_powset)
  then show ?case by blast
qed

lemma set_enumerate_eq:
  "set (enumerate n xs) = {(n + i, xs ! i) |i. i < length xs}"
  by (force simp: in_set_enumerate_eq less_diff_conv2)

lemma enumerate_Set_List_transfer [transfer_rule]:
  "((=) ===> list_all2 R ===> Set_List_rel (rel_prod (=) R))
    (\<lambda>n xs. {(n + i, xs ! i) |i. i < length xs}) enumerate"
  apply(intro rel_funI Set_List_relI rel_setI)
   apply(auto simp: set_enumerate_eq list_all2_lengthD list_all2_nthD2)
  done

definition "transl_list_list_list_set \<equiv> map set"

lemma transl_list_list_list_set_eq_map_set: "transl_list_list_list_set = map set"
  unfolding transl_list_list_list_set_def by simp

lemma list_all2_Set_List_rel_transl_list_list_list_set:
  "list_all2 Set_List_rel_eq (transl_list_list_list_set F) F"
  unfolding transl_list_list_list_set_eq_map_set
  by (auto simp: rel_set_eq list_all2_conv_all_nth)

definition "transl_set_list s \<equiv> SOME xs. set xs = s"

lemma transl_set_list_eq_Eps: "transl_set_list s = (SOME xs. set xs = s)"
  unfolding transl_set_list_def by simp

definition "transl_set_list_list_list \<equiv> map transl_set_list"

lemma transl_set_list_list_list_eq_map_transl_set_list:
  "transl_set_list_list_list = map transl_set_list"
  unfolding transl_set_list_list_list_def by simp

lemma transl_list_list_list_set_set_list_eq_self_iff_all_finite:
  "transl_list_list_list_set (transl_set_list_list_list F) = F \<longleftrightarrow> (\<forall>f \<in> set F. finite f)"
supply transl_list_list_list_set_eq_map_set[simp]
  transl_set_list_list_list_eq_map_transl_set_list[simp]
proof (induction F)
  case (Cons f F) show ?case
  proof (cases "finite f")
    case True
    then have "set (SOME xs. set xs = f) = f"
      using finite_list someI_ex[of "\<lambda>xs. set xs = f"] by blast
    with Cons True show ?thesis by (simp add: transl_set_list_eq_Eps)
  next
    case False
    then have "(transl_list_list_list_set (transl_set_list_list_list (f # F)) = f # F) \<Longrightarrow> False"
      using finite_set[of "SOME xs. set xs = f"] by (simp add: transl_set_list_eq_Eps)
    with False show ?thesis by auto
  qed
qed simp

lemma list_all2_Set_List_rel_transl_set_list_list_listI:
  assumes "\<And>f. f \<in> set F \<Longrightarrow> finite f"
  shows "list_all2 Set_List_rel_eq F (transl_set_list_list_list F)"
  using assms transl_list_list_list_set_set_list_eq_self_iff_all_finite
    list_all2_Set_List_rel_transl_list_list_list_set
  by metis

lemma finite_if_mem_if_list_all2_Set_List_rel_eq:
  assumes "list_all2 Set_List_rel_eq F G"
  and "f \<in> set F"
  shows "finite f"
  using assms by (metis finite_if_Set_List_rel_eq in_set_conv_nth list_all2_conv_all_nth)


end