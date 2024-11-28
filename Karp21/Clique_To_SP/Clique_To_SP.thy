theory Clique_To_SP
imports "../CNF_SAT_To_Clique/CNF_SAT_To_Clique" "HOL-Library.Disjoint_Sets" 
begin

definition "set_packing \<equiv> 
  {(S, l). finite S \<and> 
          (\<forall>C \<in> S. finite C) \<and> 
          (\<exists>S' \<subseteq> S. card S' = l \<and>  disjoint S')}"

lemma set_packing_cert:
  assumes "S' \<subseteq> S"
          "card S' = l"
          "disjoint S'"
          "\<forall>C \<in> S. finite C"
          "finite S"
 shows "(S,l) \<in> set_packing"
  using assms unfolding set_packing_def
  by blast


definition clique_to_set_packing:
  "clique_to_set_packing \<equiv> \<lambda>(E, V, k). if ugraph_nodes E V  then
  ((\<lambda>i. {{i,j}|j. j \<in> V  \<and> {i, j} \<notin> E }) ` V, k) else ({},1)"

lemma node_to_set_inj:
  assumes "ugraph_nodes E V"
  shows "inj_on (\<lambda>i. {{i,j}|j. j \<in> V  \<and> {i, j} \<notin> E }) V"
proof -
   have *: "{i} \<in> (\<lambda>i. {{i,j}|j. j \<in> V  \<and> {i, j} \<notin> E }) i" if "i \<in> V" for i
    using assms that
    unfolding ugraph_nodes_def ugraph_def
    by fastforce
  then show ?thesis
    by (auto simp add:  inj_on_def)
qed

lemma clique_to_set_packing_sound:
  assumes "(E, V, k) \<in> clique"
  shows "clique_to_set_packing (E, V, k) \<in> set_packing"
proof -
  obtain C where "C \<subseteq> V" and "card C \<ge> k" and "is_clique E C" and "ugraph_nodes E V"
    using assms unfolding clique_def by auto
  then obtain C' where  C'_def: "C' \<subseteq> V" "card C' = k" "is_clique E C'" 
    using assms unfolding clique_def 
    by (meson in_mono is_clique_def obtain_subset_with_card_n order.trans)
  let ?f = "(\<lambda>i. {{i,j}|j. j \<in> V \<and> {i, j} \<notin>E })"
  let ?S' = "?f ` C'"
  have "card (?f ` C') = k"
    using C'_def \<open>ugraph_nodes E V\<close> node_to_set_inj subset_inj_on
    by (intro card_image[THEN trans]) blast+
  moreover have "disjoint (?f ` C')"
    using \<open>is_clique E C'\<close> \<open>ugraph_nodes E V\<close> 
    unfolding is_clique_def ugraph_nodes_def ugraph_def  disjoint_def
    by auto (metis doubleton_eq_iff)+
  ultimately have "(?f ` V, k) \<in> set_packing"
    using \<open>ugraph_nodes E V\<close>  image_mono C'_def
    unfolding is_clique_def ugraph_nodes_def ugraph_def 
    by (intro set_packing_cert[of ?S']) auto
  then show ?thesis
      using \<open>ugraph_nodes E V\<close>
      unfolding clique_to_set_packing 
      by fastforce
qed

lemma clique_to_set_packing_complete:
  assumes "clique_to_set_packing (E, V, k) \<in> set_packing"
  shows "(E, V, k) \<in> clique"
proof (cases "ugraph_nodes E V")
  case True
  let ?f = "(\<lambda>i. {{i,j} |j. j \<in> V \<and> {i,j} \<notin> E })"
  let ?S = "?f ` V"
  from assms True obtain S' where S'_def:
    "S' \<subseteq> ?S" "card S' = k" "disjoint S'" "finite ?S" "\<forall>C \<in> ?S. finite C"
    unfolding set_packing_def clique_to_set_packing 
    by auto
 
  have "bij_betw ?f V ?S"
    using node_to_set_inj True  inj_on_imp_bij_betw by blast    
  then obtain g where g_bij: "bij_betw g ?S V" and  g_inv: "\<And>i. i \<in> V \<Longrightarrow> g (?f i) = i"
    using node_to_set_inj True bij_betw_inv_into inv_into_f_f 
    by fast
  let ?C = "g ` S'"
  have "?C \<subseteq> V" 
    using g_inv \<open>S' \<subseteq> ?S\<close> 
    by auto
  moreover{
    have "{i, j} \<in> E" if "i \<in> ?C" "j \<in> ?C" "i \<noteq> j" for i j
    proof(rule ccontr)
      assume "{i, j} \<notin> E"
      have "?f i \<in> S'" and "?f j \<in> S'" 
        using that \<open>S' \<subseteq> ?S\<close> g_inv
        by auto
      moreover have "{i,j} \<in> ?f i" and "{i,j} \<in> ?f j" 
        using \<open>{i, j} \<notin> E\<close> \<open>S' \<subseteq> ?S\<close> \<open>?C \<subseteq> V\<close> that doubleton_eq_iff[of i j j i] 
        by fastforce+
      moreover have "?f i \<noteq> ?f j" 
        using  that inj_on_subset[OF node_to_set_inj[OF True]  \<open>?C \<subseteq> V\<close>]
        by (auto simp add: inj_on_def)
      ultimately show False 
        using disjointD[OF \<open>disjoint S'\<close>, of "?f i" "?f j"]
        by blast
    qed
    then have "is_clique E ?C"
      unfolding is_clique_def by metis
  }
  moreover have "card ?C = k"
    using \<open>card S' = k\<close>  bij_betw_same_card bij_betw_subset[OF g_bij \<open>S' \<subseteq> ?S\<close>]
    by metis
  ultimately show ?thesis 
    using \<open>ugraph_nodes E V\<close>  
    unfolding clique_def
    by blast
next
  case False
  then show ?thesis 
    using assms
    unfolding clique_to_set_packing set_packing_def
    by auto
qed

theorem is_reduction_clique_to_set_packing:
  "is_reduction clique_to_set_packing clique set_packing"
  unfolding is_reduction_def 
  using clique_to_set_packing_sound clique_to_set_packing_complete
  by auto

end