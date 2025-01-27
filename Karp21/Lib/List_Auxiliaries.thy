section\<open>Auxiliaries for Lists\<close>
theory List_Auxiliaries
  imports
    Graph_Theory.Stuff
    "HOL-Library.Sublist"
begin

subsection\<open>General Proofs\<close>

lemma in_set_implies_is_nth:
  assumes "x \<in> set L"
  shows "\<exists>i. x = L!i \<and> i<length L"
  using assms by (metis in_set_conv_nth)

lemma indices_length_set_ls2:
  assumes "l = (ls1@ls2)!i" "i\<ge> length ls1" "i < length (ls1@ls2)"
  shows "l \<in> set ls2"
  using assms
  by (induction "ls1@ls2"; simp)
     (metis add_less_imp_less_left le_iff_add nth_append_length_plus nth_mem)

lemma indices_length_set_ls2_only_append:
  assumes "l = (l1#ls2)!i" "i \<ge> 1" "i< length (l1#ls2)"
  shows "l \<in> set ls2"
  using assms indices_length_set_ls2 by auto

lemma distinct_same_indices:
  assumes "distinct L" "L!i = L!j" "i<length L" "j<length L"
  shows "i = j"
  using assms by(induction L)  (auto simp add: nth_eq_iff_index_eq)

lemma length_1_set_L:
  assumes "length L = 1" "l \<in> set L"
  shows "L = [l]"
  using assms
  by (metis append_butlast_last_id butlast.simps(2) diff_is_0_eq'
      in_set_conv_nth last.simps last_conv_nth le_numeral_extra(4) length_0_conv
      length_butlast less_one list.distinct(1) zero_neq_one)

lemma last_in_set_tl:
  assumes "l = last L" "length L \<ge> 2"
  shows "l \<in> set (tl L)"
  using assms by(induction L)(auto)

lemma card_list_subset:
  assumes "s \<subseteq> set L"
  shows "card s \<le> card (set L)"
  using assms finite_subset card_mono by blast

lemma length_2_hd_last:
  assumes "length L = 2"
  shows "L = [hd L, last L]"
  using assms
  apply(induction L)
   apply(auto)
  by (metis append_butlast_last_id append_eq_append_conv append_self_conv2 length_Cons list.size(3))

lemma length_2_exits:
  assumes "length L = 2"
  shows "\<exists>l1 l2. L = [l1, l2]"
  using assms by(induction L; simp) (metis Suc_length_conv length_0_conv)

lemma length_geq_2_tt_not_empty:
  assumes "length C \<ge> 2"
  shows "tl C \<noteq> []"
  using assms  by(induction C) (auto)

lemma hd_last_eq_in_tl:
  assumes "hd xs = last xs" "x \<in> set xs" "length xs > 1"
  shows "x \<in> set (tl xs)"
  using assms by(induction xs)(auto split: if_split_asm)


subsection\<open>Sublist\<close>

lemma sublist_implies_in_set:
  assumes "sublist [v1, v2] C"
  shows "v1 \<in> set C" "v2 \<in> set C"
  using assms by(auto simp add: sublist_def)

lemma sublist_implies_in_set_a:
  assumes "sublist [v1, v2] C" "distinct C"
  shows "v1 \<noteq> v2"
  using assms by (auto simp add: sublist_def)

lemma sublist3_hd_lists:
  assumes "distinct L" "L = l1#ls1 @ ls2" "sublist [v1, v2] L" "v1 = l1"
  shows "v2 = hd (ls1 @ ls2)"
  using assms unfolding sublist_def
  by(induction L; simp)
    (metis assms(1, 2) distinct_append hd_append hd_in_set list.sel(1, 3)
      not_distinct_conv_prefix self_append_conv2)

lemma sublist_set_ls2_1:
  assumes "distinct L" "L = ls1 @ ls2" "sublist [v1, v2] L" "v1 \<in> set ls2"
  shows "v2 \<in> set ls2"
  using assms
proof(induction L arbitrary: ls2 ls1)
  case Nil
  then show ?case by auto
next
  case (Cons a L)
  then show ?case proof(cases "v1 = a")
    case True
    then have "ls1 = []"
      using assms Cons
      by (metis (no_types, opaque_lifting) Nil_is_append_conv append.assoc append_Cons_eq_iff
          append_self_conv2 distinct.simps(2) in_set_conv_decomp list.distinct(1) split_list)
    then have "a#L = ls2"
      using Cons
      by auto
    then have "v2 \<in> set ls2"
      using Cons sublist_implies_in_set(2)
      by metis
    then show ?thesis .
  next
    case False
    then obtain p1 p2 where p_def: "p1@ [v1, v2] @ p2 =a#L"
      using Cons unfolding sublist_def by auto
    then have L_def_2: "L = tl( p1@ [v1, v2] @ p2)"
      by auto
    have "p1 \<noteq> []"
      using False Cons p_def
      by (metis append_self_conv2 hd_append2 list.sel(1) list.sel(2) list.sel(3) not_Cons_self2)
    then have "L = (tl p1) @ [v1, v2] @ p2"
      using L_def_2
      by simp
    then show ?thesis
      using Cons sublist_def
      by (metis L_def_2 append_self_conv2 sublist_implies_in_set(2) distinct_tl p_def tl_append2)
  qed
qed

lemma sublist_set_ls2_2:
  assumes "distinct L" "L = l1 # ls1 @ ls2" "sublist [v1, v2] L" "v1 \<in> set ls2"
  shows "v2 \<in> set ls2"
  using assms sublist_set_ls2_1 by (metis Cons_eq_appendI)

lemma sublist_set_ls2_3:
  assumes "distinct L" "L = ls1 @ ls2" "sublist [v1, v2] L" "v1 \<in> set ls2"
  shows "sublist [v1, v2] ls2"
  using assms
proof(induction L arbitrary: ls2 ls1)
  case Nil
  then show ?case by auto
next
  case (Cons a L)
  then show ?case
  proof(cases "v1 = a")
    case True
    then have "ls1 = []"
      using assms Cons
      by (metis (no_types, opaque_lifting) Nil_is_append_conv append.assoc
          append_Cons_eq_iff append_self_conv2 distinct.simps(2) in_set_conv_decomp
          list.distinct(1) split_list)
    then have "a#L = ls2"
      using Cons
      by auto
    then show ?thesis
      using Cons
      by blast
  next
    case False
    then obtain p1 p2 where p_def: "p1@ [v1, v2] @ p2 =a#L"
      using Cons unfolding sublist_def by auto
    then have L_def_2: "L = tl( p1@ [v1, v2] @ p2)"
      by auto
    have "p1 \<noteq> []"
      using False Cons p_def
      by (metis append_self_conv2 hd_append2 list.sel(1) list.sel(2) list.sel(3) not_Cons_self2)
    then have "L = (tl p1) @[v1, v2] @ p2"
      using L_def_2
      by simp
    then show ?thesis
      using Cons sublist_def
      by (metis L_def_2 append_self_conv2 distinct_tl p_def tl_append2)
  qed
qed

lemma sublist_set_ls2_4:
  assumes "distinct L" "L = l1 # ls1 @ ls2" "sublist [v1, v2] L" "v1 \<in> set ls2" "ls3 = l1 # ls1"
  shows "sublist [v1, v2] ls2"
proof -
  have 1: "L = ls3 @ ls2"
    using assms
    by simp
  then have 1: "sublist [v1, v2] ls2"
    using sublist_set_ls2_3 assms 1 by metis
  then show ?thesis
    by (auto simp add: sublist_def)
qed

lemma sublist_set_ls2:
  assumes "distinct L" "L = l1 # ls1 @ ls2" "sublist [v1, v2] L" "v1 \<in> set ls2"
  shows  "sublist [v1, v2] ls2"
  using assms sublist_set_ls2_4 by metis

lemma sublist_set_ls1_1:
  assumes "distinct L" "L = ls1 @ ls2" "sublist [v1, v2] L" "v1 \<in> set ls1" "v1 \<noteq> last ls1"
  shows "v2 \<in> set ls1"
  using assms
proof(induction L arbitrary: ls1 ls2 )
  case Nil
  then show ?case
    by auto
next
  case (Cons a L)
  then show ?case
  proof(cases "v1 = a")
    case True
    then have "v1 = hd ls1"
      using Cons
      by (metis distinct.simps(2) distinct_singleton hd_append2 list.sel(1))
    with Cons have "v1 \<noteq> last ls1"
      by auto
    then have "tl ls1 \<noteq> []"
      using \<open>v1 = hd ls1\<close>
      by (metis Cons.prems(4) distinct.simps(2) distinct_singleton last_ConsL list.collapse)
    obtain p1 p2 where "p1@ [v1, v2] @ p2 = (a#L)"
      using Cons assms sublist_def by metis
    then have "p1 = []"
      using Cons \<open>v1 = a\<close> sublist_def
      by (metis sublist_implies_in_set(1) distinct.simps(2) list.sel(3) tl_append2)
    then have "v2 = hd L"
      using Cons \<open>p1 @ [v1, v2] @ p2 = a # L\<close>
      by (metis Cons_eq_appendI True eq_Nil_appendI list.sel(1) list.sel(3))
    then have "v2 = hd (tl ls1)"
      using Cons \<open>tl ls1 \<noteq> []\<close>  \<open>p1 = []\<close> by (metis Nil_tl hd_append2 list.sel(3) tl_append2)
    then show ?thesis
      by (simp add: \<open>tl ls1 \<noteq> []\<close> list_set_tl)
  next
    case False
    then obtain p1 p2 where p_def: "p1@ [v1, v2] @ p2 =a#L"
      using Cons
      by (auto simp add: sublist_def)
    then have L_def_2: "L = tl( p1@ [v1, v2] @ p2)"
      by auto
    have "p1 \<noteq> []"
      using False Cons p_def
      by (metis hd_append2 list.sel(1) list.sel(2) list.sel(3) not_Cons_self2 self_append_conv2)
    then have "L = (tl p1) @[v1, v2] @ p2"
      using L_def_2
      by simp
    then have 1: "\<exists>p1 p2. p1@ [v1, v2] @ p2 = L"
      by auto
    have 2: "distinct L"
      using Cons
      by (meson distinct.simps(2))
    have 3: "L = tl ls1 @ ls2"
      using Cons
      by (metis distinct.simps(2) distinct_singleton list.sel(3) tl_append2)
    have 4: "v1 \<in> set (tl ls1)"
      using Cons False
      by (metis hd_Cons_tl hd_append2 list.sel(1) set_ConsD tl_Nil)
    have 5: "v1 \<noteq> last (tl ls1)"
      using Cons
      by (metis "4" last_tl list.set_cases neq_Nil_conv)
    then show ?thesis
      using Cons 1 2 3 4 5 list_set_tl sublist_def
      by metis
  qed
qed

lemma sublist_cons_impl_sublist_list:
  assumes "sublist (a#as) (c#cs)" "a \<noteq> c"
  shows "sublist (a#as) cs"
  by (meson Cons_prefix_Cons assms sublist_Cons_right)

lemma sublist_cons_impl_sublist:
  assumes "sublist [a, b] (c#cs)" "a \<noteq> c"
  shows "sublist [a, b] cs"
  using assms sublist_cons_impl_sublist_list by metis

lemma sublist_second_not_hd:
  assumes "distinct L" "sublist [v1, v2] L"
  shows "v2 \<noteq> hd L"
  using assms
proof(induction L)
  case Nil
  then show ?case
    by (auto simp add: sublist_def)
next
  case (Cons a L)
  then have 1: "v1 \<noteq> v2"
    by (meson sublist_implies_in_set_a)
  then show ?case
  proof(cases "v1 = hd (a#L)")
    case True
    then show ?thesis
      using 1 by auto
  next
    case False
    then have "sublist [v1, v2] L"
      using Cons sublist_cons_impl_sublist by (metis list.sel(1))
    then show ?thesis
      using Cons sublist_implies_in_set(2) by force
  qed
qed

lemma sublist_set_ls1_2:
  assumes "distinct L" "L = l1 # ls1 @ ls2" "sublist [v1, v2] L" "v1 \<in> set ls1"
    "v1 \<noteq> last ls1" "ls3 = l1 # ls1"
  shows "v2 \<in> set ls1"
  using assms
  by (metis distinct.simps(2) hd_append2 length_greater_0_conv length_pos_if_in_set
      list.set_sel(1) sublist3_hd_lists sublist_cons_impl_sublist sublist_set_ls1_1)

lemma sublist_set_ls1_3:
  assumes "distinct L" "L = l1#ls1 @ ls2" "sublist [v1, v2] L" "v1 \<in> set ls1" "v1 \<noteq> last ls1"
  shows "v2 \<in> set ls1"
  using assms sublist_set_ls1_2 sublist_def by fast

lemma sublist_set_ls1_4:
  assumes "distinct L" "L = ls1 @ ls2" "sublist [v1, v2] L" "v1 \<in> set ls1" "v1 \<noteq> last ls1"
  shows "sublist [v1, v2] ls1"
  using assms
  apply (simp add: sublist_append)
  apply safe
  subgoal sublist_ls2
    by (metis disjoint_iff_not_equal sublist_implies_in_set(1))
  subgoal for xs1 xs2
    by (auto 4 3 simp add: Cons_eq_append_conv suffix_def intro: sublist_ls2)
  done

lemma sublist_set_ls1:
  assumes "distinct L" "L = l1#ls1 @ ls2" "sublist [v1, v2] L" "v1 \<in> set ls1" "v1 \<noteq> last ls1"
  shows "sublist [v1, v2] ls1"
  by (metis Un_iff assms distinct.simps(2) set_append sublist_cons_impl_sublist sublist_set_ls1_4)

lemma sublist_set_last_ls1_2:
  assumes "x = hd L" "x = last ls1" "L = ls1 @ ls2" "x \<in> set ls1" "distinct L"
  shows "ls1 = [x]"
  using assms
  by (induction L arbitrary: ls1 ls2; simp)
     (metis distinct.simps(2) hd_append2 hd_in_set in_set_conv_decomp_first
       last_in_set last_tl list.sel(3) self_append_conv2)

lemma sublist_set_last_ls1_1:
  assumes "distinct L" "L = ls1 @ ls2" "sublist [v1, v2] L" "v1 = last ls1" "v1 \<in> set ls1"
  shows "v2 = hd ls2"
  using assms
proof(induction L arbitrary: ls1 ls2)
  case Nil
  then show ?case
    by auto
next
  case (Cons a L)
  then show ?case
  proof(cases "v1 = a")
    case True
    then have "v1 = hd (a#L)"
      by simp
    then have "ls1 = [a]"
      using assms Cons sublist_set_last_ls1_2 True
      by fast
    then have "L = ls2"
      using Cons
      by auto
    then show ?thesis
      using Cons \<open>ls1 = [a]\<close>
      by (metis (mono_tags, lifting) Cons_eq_appendI True sublist3_hd_lists  list.sel(3))
  next
    case False
    then obtain p1 p2 where p_def: "p1@ [v1, v2] @ p2 =a#L"
      using Cons
      by (auto simp add: sublist_def)
    then have L_def_2: "L = tl( p1@ [v1, v2] @ p2)"
      by auto
    have "p1 \<noteq> []"
      using False Cons p_def
      by (metis append_self_conv2 hd_append2 list.sel(1) list.sel(2) list.sel(3) not_Cons_self2)
    then have L_exists: "L = (tl p1) @[v1, v2] @ p2"
      using L_def_2
      by simp
    have "ls1 \<noteq> []"
      using False Cons
      by auto
    then have "L = tl ls1 @ ls2"
      using Cons
      by (metis list.sel(3) tl_append2)
    then show ?thesis
      using Cons L_exists sublist_def False
      by (metis distinct.simps(2) distinct_singleton hd_append2
          last_tl list.collapse list.sel(1) set_ConsD)
  qed
qed

lemma sublist_set_last_ls1_1_1:
  assumes "distinct L" "L = ls1 @ ls2" "sublist [v1, v2] L" "v1 = last ls1" "v1 \<in> set ls1"
  shows "v2 \<in> set ls2"
  using assms
  by (metis append_Nil2 append_butlast_last_id list.set_intros(1) list.set_sel(1) set_ConsD
        sublist_implies_in_set_a sublist_set_last_ls1_1 sublist_set_ls2_1)

lemma sublist_set_last_ls1_3:
  assumes "distinct L" "L = l1#ls1 @ ls2" "sublist [v1, v2] L"
    "v1 = last ls1" "v1 \<in> set ls1" "ls3 = l1 # ls1"
  shows "v2 = hd ls2"
  using assms
  by (metis Cons_eq_appendI distinct.simps(2) last.simps list.set_intros(1)
      sublist_cons_impl_sublist_list sublist_set_last_ls1_1)

lemma sublist_set_last_ls1:
  assumes "distinct L" "L = l1#ls1 @ ls2" "sublist [v1, v2] L" "v1 = last ls1" "v1 \<in> set ls1"
  shows "v2 = hd ls2"
  using assms sublist_set_last_ls1_3 by fast

lemma sublist_set_noteq_l1:
  assumes "distinct (tl L)" "L = l1#ls1 @ ls2" "sublist [v1, v2] L" "v1 \<noteq> l1"
  shows "sublist [v1, v2] (ls1@ls2)"
  using assms unfolding sublist_def
  by (induction L; simp) (metis append_self_conv2 assms(2,4) list.inject list.sel(3) tl_append2)

lemma sublist_set_v2_noteq_hd_lists:
  assumes "distinct (tl L)" "L = l1#ls1 @ ls2" "sublist [v1, v2] L" "v2 \<noteq> hd (ls1@ls2)"
  shows "sublist [v1, v2] (ls1@ls2)"
  using assms unfolding sublist_def
  by(induction L; simp) (metis append_self_conv2 list.sel(1) list.sel(3) tl_append2)

lemma sublist_v1_in_subsets:
  assumes "sublist [v1, v2] L" "L = l1@l2"
  shows "v1 \<in> set l1 \<or> v1 \<in> set l2"
  using assms
  by(induction L arbitrary: l1 l2; simp add: sublist_def)
    (metis hd_append2 in_set_conv_decomp list.sel(1) list.sel(3)
      list.set_sel(1) list_set_tl self_append_conv2 tl_append2)

lemma sublist_v1_hd_v2_hd_tl:
  assumes "sublist [v1, v2] L" "distinct L" "v1 = hd L"
  shows "v2 = hd(tl L)"
  using assms
  by (induction L arbitrary: v1; simp add: sublist_def)
     (metis in_set_conv_decomp list.sel(1) list.sel(3) self_append_conv2 tl_append2)

lemma sublist_v1_hd_v2_hd_tl_lists:
  assumes "p1@ (v#vs) @ p2 = L" "distinct L" "v = hd L"
  shows "vs @ p2 = tl L"
  using assms
  by (induction L arbitrary: v vs; simp)
     (metis append_self_conv2 in_set_conv_decomp list.sel(3) tl_append2)

lemma sublist_append:
  assumes "sublist l1 l2"
  shows "sublist l1 (l3@l2)"
  using assms append_eq_append_conv2 unfolding sublist_def by blast

lemma sublist_cons:
  assumes "sublist l1 l2"
  shows "sublist l1 (l#l2)"
  using assms by (metis Cons_eq_appendI sublist_def)

lemma two_sublist_distinct_same_first:
  assumes "sublist [x, a] L" "sublist [y, a] L" "distinct (tl L)"
  shows "x = y"
  using assms
proof(induction L)
  case Nil
  then show ?case
    by (simp add: sublist_def)
next
  case (Cons l L)
  then have distinct: "distinct L"
    by simp
  then have 1: "distinct (tl L)"
    by (simp add: distinct_tl)
  then show ?case
  proof(cases "sublist [x, a] L")
    case True
    then have a1: "sublist [x, a] L"
      by simp
    then show ?thesis
    proof(cases "sublist [y, a] L")
      case True
      then show ?thesis
        using a1 1 Cons
        by simp
    next
      case False
      then have 2: "\<exists>p1 p2. p1@[y, a] @ p2 = (l#L)" "\<not> (\<exists>p1 p2. p1@[y, a] @ p2 = (L))"
        using sublist_def Cons by metis+
      then have "y = l"
        using Cons False by (meson sublist_cons_impl_sublist)
      then have hd: "a = hd L"
        by (metis 2 append_self_conv2 hd_append2 list.distinct(1) list.sel(1) list.sel(3) tl_append2)
      have tl: "a \<in> set (tl L)"
        using a1 distinct hd sublist_second_not_hd by fastforce
      then have False
        using hd tl distinct
        by (metis distinct.simps(2) distinct_singleton list.collapse list_set_tl)
      then show ?thesis
        by simp
    qed
  next
    case False
    then have 2: "\<exists>p1 p2. p1@[x, a] @ p2 = (l#L)" "\<not> (\<exists>p1 p2. p1@[x, a] @ p2 = (L))"
      using sublist_def Cons by metis+
    then have 3: "x = l"
      using Cons False by (meson sublist_cons_impl_sublist)
    then show ?thesis
    proof(cases "sublist [y, a] L")
      case True
      then have hd: "a = hd L"
        by (metis 2 append_self_conv2 hd_append2 list.distinct(1) list.sel(1) list.sel(3) tl_append2)
      have tl: "a \<in> set (tl L)"
        using 3 True sublist_def False
        by (smt append_Cons list.sel(3) list.set_intros(1) self_append_conv2
            sublist_implies_in_set(2) tl_append2)
      then have False
        using hd tl distinct
        by (metis distinct.simps(2) distinct_singleton list.collapse list_set_tl)
      then show ?thesis
        by simp
    next
      case False
      then have 2: "\<exists>p1 p2. p1@[y, a] @ p2 = (l#L)" "\<not> (\<exists>p1 p2. p1@[y, a] @ p2 = (L))"
        using sublist_def Cons by metis+
      then have "y = l"
        using Cons False by (meson sublist_cons_impl_sublist)
      then show ?thesis using 3
        by simp
    qed
  qed
qed

lemma sublist_not_cyclic_for_distinct:
  assumes "sublist [a, b] Cy" "sublist [b, a] Cy" "distinct Cy"
  shows False
  using assms unfolding sublist_def
  by simp
     (metis assms distinct_append list.sel(1) list.set_intros(1)
       sublist_second_not_hd sublist_set_ls2_1 sublist_set_ls2_3)

lemma distinct_sublist_last_first_of_sublist_false:
  assumes "distinct cs" "sublist [a, b] cs" "a = last cs"
  shows False
  using assms unfolding sublist_def
  by simp
     (metis append.right_neutral assms(2) distinct.simps(2) distinct_singleton
       sublist_implies_in_set(1) sublist_set_last_ls1_1_1)

lemma distinct_sublist_last_first_of_sublist_false_2:
  assumes "distinct cs" "sublist [a, b, b2] cs" "a = last cs"
  shows False
  by (smt append_Cons append_Cons_eq_iff append_butlast_last_id assms distinct.simps(2)
        distinct_append list.distinct(1) not_distinct_conv_prefix sublist_code(2) sublist_def)

lemma sublist_hd_tl_equal_b_hd_tl:
  assumes "sublist [a, b] cs" "distinct (tl cs)" "a = last cs"
  shows "b = hd (tl cs)"
  by (metis append_Nil2 assms distinct_sublist_last_first_of_sublist_false hd_Cons_tl last_tl
        sublist_code(2) sublist_set_v2_noteq_hd_lists)

lemma sublist_hd_tl_equal_b_hd_tl_2:
  assumes "sublist [a, b, c] cs" "distinct (tl cs)" "a = last cs"
  shows "b = hd (tl cs) \<and> c = hd(tl (tl cs))"
  by (smt append_is_Nil_conv assms distinct_sublist_last_first_of_sublist_false_2 hd_append2
       last_appendR list.distinct(1) list.sel(1) list.sel(3) self_append_conv2 sublist_def
       tl_append2)

lemma sublist_hd_last_only_2_elems:
  assumes "sublist [a,b] cs" "a = hd cs" "b = last cs" "distinct cs"
  shows "cs = [a, b]"
  by (smt assms distinct1_rotate hd_append last.simps list.exhaust_sel list.set_intros(1)
        rotate1_hd_tl sublist_cons sublist_order.order.eq_iff
        sublist_set_last_ls1_2 sublist_v1_hd_v2_hd_tl)

lemma two_sublist_distinct_same_last:
  assumes "sublist [x, a] L" "sublist [x, b] L" "distinct (L)"
  shows "a = b"
  using assms unfolding sublist_def
  by (induction L; simp)
     (metis append_self_conv2 in_set_conv_decomp list.sel(1) list.sel(3) tl_append2)

lemma sublist_append_not_in_first:
  assumes "sublist [v1, v2] (l1 @ l2)" "v1 \<notin> set l1"
  shows "sublist [v1, v2] l2"
  using assms by(induction l1)(auto simp add: sublist_cons_impl_sublist)

lemma sublist_append_using_or:
  assumes "sublist [a, b] (l1@l2)" "distinct (l1@l2)" "l1 \<noteq> []"
  shows "sublist [a, b] l1 \<or> sublist [a, b] l2 \<or> (a = last l1 \<and> b = hd l2)"
  using assms by (metis sublist_append_not_in_first sublist_set_last_ls1_1 sublist_set_ls1_4)

lemma distinct_tl_rev_C:
  assumes "distinct (tl C)" "hd C = last C \<or> distinct C"
  shows "distinct (tl (rev C))"
  by (smt List.butlast_rev append_butlast_last_id append_is_Nil_conv assms distinct_append
        distinct_rev hd_append2 last_rev rev_is_Nil_conv set_rev tl_append2 tl_rev)

lemma b_in_set_cy_exists_sublist:
  assumes "b \<in> set Cy" "b \<in> set (tl Cy)" "length Cy \<ge> 2"
  shows "\<exists>a. sublist [a, b] Cy"
  using assms
proof(induction Cy)
  case Nil
  then show ?case
    by auto
next
  case (Cons c Cy)
  then have 1: "b \<in> set Cy"
    by simp
  then show ?case
  proof(cases "b = hd Cy")
    case True
    then have "(c#Cy) = c#b#tl Cy"
      by (metis 1 hd_Cons_tl list.distinct(1) list.set_cases)
    then have "[]@[c,b]@tl Cy = c#Cy"
      by simp
    then have "sublist [c, b] (c#Cy)"
      using Cons sublist_def by metis
    then show ?thesis
      by auto
  next
    case False
    have 2: "length Cy \<ge> 2"
    proof (rule ccontr)
      assume "\<not> 2 \<le> length Cy"
      then have "2 > length Cy"
        by auto
      then have "length Cy = 0 \<or> length Cy = 1"
        by linarith
      then show False
      proof
        assume "length Cy = 0"
        then have "Cy = []"
          by simp
        then show False
          using 1
          by simp
      next
        assume "length Cy = 1"
        then have "Cy = [b]"
          using 1 length_1_set_L
          by metis
        then have "hd Cy = b"
          by simp
        then show False
          using False
          by simp
      qed
    qed
    then have 3: "b \<in> set (tl Cy)"
      using False
      by (metis "1" list.sel(1) list.sel(3) list.set_cases)
    then have "\<exists>a. sublist [a, b] Cy"
      using Cons 1 2 3 False
      by blast
    then show ?thesis
      using 2 sublist_cons
      by fast
  qed
qed

lemma a_in_set_cy_exists_sublist:
  assumes "a \<in> set Cy" "a\<noteq> last Cy"
  shows "\<exists>b. sublist [a, b] Cy"
  by (metis append_Cons append_Nil assms hd_Cons_tl in_set_conv_decomp last_snoc sublist_appendI
        sublist_order.order.eq_iff sublist_order.order.trans)

lemma b_in_Cycle_exists_sublist:
  assumes "b \<in> set Cycle" "length Cycle \<ge> 2" "hd Cycle = last Cycle"
  shows "\<exists>a. sublist [a, b] Cycle"
  using assms by (metis b_in_set_cy_exists_sublist hd_Cons_tl last_in_set_tl list.sel(2) set_ConsD)

lemma a_in_Cycle_exists_sublist:
  assumes "a \<in> set Cycle" "length Cycle \<ge> 2" "hd Cycle = last Cycle"
  shows "\<exists>b. sublist [a, b] Cycle"
  using assms
proof(cases "a = last Cycle")
  case True
  then have 1: "a = hd Cycle"
    using assms
    by simp
  then obtain b where "b = hd (tl Cycle)"
    by simp
  then have 2: "a # tl Cycle = Cycle"
    using 1 by (metis assms(1) hd_Cons_tl list.discI list.set_cases)
  have "tl Cycle \<noteq> []"
    using last_in_set_tl assms
    by fastforce
  then have "[]@[a, b] @ (tl (tl Cycle)) = Cycle"
    using 2
    by (simp add: \<open>b = hd (tl Cycle)\<close>)
  then have "sublist [a, b] Cycle"
    using sublist_def by metis
  then show ?thesis
    by auto
next
  case False
  then show ?thesis
    using a_in_set_cy_exists_sublist assms
    by metis
qed

lemma two_sublist_same_first_distinct_tl:
  assumes "distinct (tl cs)" "sublist [x, a] cs" "sublist [x, b] cs" "hd cs = last cs"
  shows "b = a"
  using assms
  by (metis distinct.simps(1) list.collapse sublist_cons_impl_sublist_list
      sublist_hd_tl_equal_b_hd_tl two_sublist_distinct_same_last)

lemma distinct_tl_cyclic_sublist_cs_explisit:
  assumes "distinct (tl cs)" "sublist [a, b] cs" "sublist [b, a] cs" "hd cs = last cs" "b \<noteq> a"
  shows "cs = [a, b, a] \<or> cs = [b, a, b]"
  using assms
proof(cases "a = hd cs")
  case True
  then have 1: "b = hd (tl cs)"
    using assms sublist_hd_tl_equal_b_hd_tl
    by fastforce
  then have 2: "a = hd (tl (tl cs))"
    by (metis True assms distinct.simps(1) distinct_singleton hd_Cons_tl
        last_tl list.sel(1) list.sel(3) sublist_cons_impl_sublist sublist_hd_last_only_2_elems
        sublist_not_cyclic_for_distinct)
  then have "cs = [a, b, a]@ (tl (tl (tl cs)))"
    using 1 2 True
    by (metis append_Nil2 assms(1) assms(3) assms(4) assms(5) last_tl list.collapse list.sel(2)
        list.sel(3) sublist_cons_impl_sublist sublist_hd_last_only_2_elems)
  have "a = last cs"
    using assms True
    by simp
  then show ?thesis
    using assms 1 \<open>cs = [a, b, a] @ tl (tl (tl cs))\<close>
    by (metis last_tl list.collapse self_append_conv sublist_cons_impl_sublist
        sublist_hd_last_only_2_elems tl_Nil)
next
  case False
  then have 1: "sublist [a, b] (tl cs)"
    using assms
    by (metis distinct.simps(1) hd_Cons_tl sublist_cons_impl_sublist sublist_not_cyclic_for_distinct)
  then show ?thesis proof(cases "b = hd cs")
    case True
    then have 1: "a = hd (tl cs)"
      using assms sublist_hd_tl_equal_b_hd_tl
      by fastforce
    then have 2: "b = hd (tl (tl cs))"
      by (metis True assms distinct.simps(1) distinct_singleton hd_Cons_tl last_tl list.sel(1, 3)
          sublist_cons_impl_sublist sublist_hd_last_only_2_elems sublist_not_cyclic_for_distinct)
    then have "cs = [b, a, b]@ (tl (tl (tl cs)))"
      using 1 2 True
      by (metis append_Nil2 assms(1, 2, 4, 5) last_tl list.collapse list.sel(2, 3)
          sublist_cons_impl_sublist sublist_hd_last_only_2_elems)
    have "b = last cs"
      using assms True
      by simp
    then show ?thesis
      using assms 1 \<open>cs = [b, a, b] @ tl (tl (tl cs))\<close>
      by (metis last_tl list.collapse self_append_conv sublist_cons_impl_sublist
          sublist_hd_last_only_2_elems tl_Nil)
  next
    case False
    then have 2: "sublist [b, a] (tl cs)"
      using assms
      by (metis distinct.simps(1) hd_Cons_tl sublist_cons_impl_sublist
          sublist_not_cyclic_for_distinct)
    then show ?thesis
      using 1 2 assms
      by (meson sublist_not_cyclic_for_distinct)
  qed
qed

lemma sublist_rev:
  assumes "sublist as bs"
  shows "sublist (rev as) (rev bs)"
  using assms sublist_def by (metis append.assoc rev_append)

lemma sublist_ab_bc_b_not_head:
  assumes "sublist [a, b] ds" "sublist [b, c] ds" "b \<noteq> hd ds""distinct (tl ds)"
  shows "sublist [a, b, c] ds"
  using assms
proof(induction ds)
  case Nil
  then have "[] \<noteq> []"
    by (simp add: sublist_def)
  then show ?case
    by simp
next
  case (Cons d ds)
  then show ?case
  proof(cases "b = hd ds")
    case True
    have "distinct ds" using Cons by auto
    then have 1: "c = hd (tl ds)"
      using True Cons
      by (metis list.sel(1) list.sel(3) sublist_cons_impl_sublist sublist_v1_hd_v2_hd_tl)
    have 2: "a = d"
      using True Cons
      by (metis (no_types, lifting) Cons_eq_appendI \<open>distinct ds\<close> append_self_conv2
          distinct_rev distinct_sublist_last_first_of_sublist_false last_rev rev.simps(1, 2)
          sublist_cons_impl_sublist sublist_not_cyclic_for_distinct sublist_rev)
    then have "ds = b # c # tl(tl ds)"
      using 1 2 True
      by (metis Cons.prems(1, 2, 3) True distinct_length_2_or_more distinct_singleton
          distinct_sublist_last_first_of_sublist_false last_ConsL last_ConsR list.collapse list.sel(1))
    then have "d#ds = a # b #c #(tl (tl ds))"
      using 2
      by simp
    then have "d#ds = [] @ [a, b, c] @ (tl (tl ds))"
      by simp
    then show ?thesis
      using sublist_def
      by metis
  next
    case False
    then have 1: "sublist [a, b] ds"
      using Cons
      by (metis append_self_conv2 hd_append2 list.distinct(1) list.sel(1, 3) sublist_def tl_append2)
    then have 2: "sublist [b, c] ds"
      using Cons list.sel(1) sublist_cons_impl_sublist
      by metis
    then show ?thesis
      using 1 2 Cons
      by (simp add: False distinct_tl sublist_cons)
  qed
qed

lemma sublist_ab_bcs_b_not_head:
  assumes "sublist [a, b] ds" "sublist (b#cs) ds" "b \<noteq> hd ds""distinct (tl ds)"
  shows "sublist (a#b#cs) ds"
  using assms
proof(induction ds)
  case Nil
  then have "[] \<noteq> []"
    by (simp add: sublist_def)
  then show ?case
    by simp
next
  case (Cons d ds)
  then obtain p1 p2 where p_def: "p1 @ (b#cs) @ p2 = d#ds"
    using sublist_def by metis
  then show ?case
  proof(cases "b = hd ds")
    case True
    have "distinct ds"
      using Cons
      by auto
    then have 1: "cs@p2 = tl ds"
      using True Cons p_def sublist_v1_hd_v2_hd_tl_lists
      by (metis hd_append list.sel(1, 2, 3) not_Cons_self2 tl_append2)
    have 2: "a = d"
      using True Cons \<open>distinct ds\<close>
      by (metis (no_types, lifting) Cons_eq_appendI append_self_conv2 distinct_rev
          distinct_sublist_last_first_of_sublist_false last_rev rev.simps(1, 2)
          sublist_cons_impl_sublist sublist_not_cyclic_for_distinct sublist_rev)
    then have "ds = b # cs @ p2"
      using 1 2 True
      by (metis Cons.prems(1) True distinct_singleton distinct_sublist_last_first_of_sublist_false
          last_ConsL list.collapse)
    then have "d#ds = a # b #cs @p2"
      using 2
      by simp
    then have "d#ds = [] @ (a# b#cs) @ p2"
      by simp
    then show ?thesis
      using sublist_def
      by metis
  next
    case False
    then have 1: "sublist [a, b] ds"
      using Cons
      by (metis append_self_conv2 hd_append2 list.distinct(1) list.sel(1, 3) sublist_def tl_append2)
    then have 2: "sublist (b#cs) ds"
      using Cons list.sel(1) sublist_cons_impl_sublist_list
      by metis
    then show ?thesis
      using 1 2 Cons
      by (simp add: False distinct_tl sublist_cons)
  qed
qed

lemma sublist_indixes:
  assumes "Suc i < length cs"
  shows "sublist [cs!i, cs!Suc i] cs"
  using assms
proof(induction cs arbitrary: i)
  case Nil
  then show ?case
    by simp
next
  case (Cons a cs)
  then show ?case proof(cases "Suc i = 1")
    case True
    then have "i = 0"
      by simp
    then have "(a#cs)!i = a"
      using Cons.prems hd_conv_nth
      by fastforce
    then have "(a#cs)!Suc i = hd (cs)"
      using Cons
      by (simp add: \<open>i = 0\<close> hd_conv_nth)
    then have "(a#cs) = [(a#cs)!i, (a#cs)!Suc i] @ tl cs"
      using Cons.prems \<open>i = 0\<close>
      by auto
    then have "(a#cs) = [] @ [(a#cs)!i, (a#cs)!Suc i] @ tl cs"
      using Cons.prems \<open>i = 0\<close>
      by auto
    then show ?thesis
      using sublist_def
      by metis
  next
    case False
    then have "Suc i > 1"
      by simp
    then have "Suc i -1 < length cs"
      using Cons
      by fastforce
    then have "sublist [cs!(i-1), cs!i] cs"
      using Cons \<open>1 < Suc i\<close> gr0_conv_Suc by auto
    then show ?thesis
      by (metis One_nat_def Suc_less_SucD \<open>1 < Suc i\<close> nth_Cons_Suc nth_Cons_pos sublist_cons)
  qed
qed

lemma sublist_sublist_hd:
  assumes "sublist (x#b) C"  "b \<noteq> []"
  shows "sublist [x, hd b] (C)"
  by (metis Cons_eq_appendI assms list.collapse self_append_conv2 sublist_append_rightI
        sublist_order.order.trans)

lemma sublist_cons_cons:
  assumes "sublist (a#b) (c#C)"
  shows "sublist b C"
  by (meson assms Cons_prefix_Cons prefix_imp_sublist sublist_Cons_right sublist_order.order.trans
        sublist_order.order_refl)

lemma hd_C_sublist_hd:
  assumes "distinct (tl C) \<and> hd C = last C  \<or> distinct C" "hd C = x" "sublist (x#b) C"
  shows "\<exists>p. C = (x#b) @ p"
  using assms
proof(induction C arbitrary: x b)
  case Nil
  then show ?case
    by (auto simp add: sublist_def)
next
  case (Cons a C)
  then show ?case
  proof(cases "b = []")
    case True
    then show ?thesis
      using Cons
      by auto
  next
    case False
    then have 1: "sublist b C"
      using Cons sublist_cons_cons
      by metis
    then have "hd C = hd b"
    proof -
      have "sublist [x, hd b] (a#C)"
        using Cons sublist_sublist_hd False
        by metis
      then have "hd b = hd C"
        using Cons
        by (metis list.sel(3) sublist_hd_tl_equal_b_hd_tl sublist_v1_hd_v2_hd_tl)
      then show ?thesis by auto
    qed
    then have "\<exists>p. C = b @ p"
      using Cons 1
      by (metis False distinct_tl list.collapse list.sel(3))
    then show ?thesis
      using Cons.prems(2)
      by auto
  qed
qed

end