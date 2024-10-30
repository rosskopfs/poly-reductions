theory XC_To_ST_Karp72
  imports "../SAT_To_XC/XC_Definition"
          "../X3C_To_ST/ST_Definition"         
begin


(* reduction from "Karp, R. M. (1972). Reducibility among combinatorial problems" *)

datatype 'a red_vertex = a 'a | ROOT |  c "'a set"

definition w_red :: "('a red_vertex) edge \<Rightarrow> nat" where
  "w_red e \<equiv> (if \<exists>s. e = {ROOT, c s} then card (THE s. e = {ROOT, c s}) else 0)"

definition XC_to_steiner_tree ::
    "'a set \<times> 'a set set  \<Rightarrow> ('a red_vertex) steiner_tree_tuple " where
   "XC_to_steiner_tree \<equiv> \<lambda>(X, S).
   ( (a ` X) \<union> {ROOT} \<union> (c ` S),
     {{ROOT, c s} | s. s \<in> S} \<union> {{c u, a v} | u v. u \<in> S \<and> v \<in> u}, w_red,
     {ROOT} \<union>  (a ` X),
     card X)"


lemma total_w_is_sum_card:
  assumes "tree Tv Te"
  assumes "{x \<in> Te. \<exists>s. x = {ROOT, c s}} = {{ROOT, c s}|s. s \<in> S'}"
  shows "(\<Sum>e \<in> Te. w_red e) =  sum card S'"
proof -
  interpret T: tree Tv Te using assms by auto
  have "(\<Sum>e \<in> Te. w_red e) = sum (\<lambda>e. card (THE s. e = {ROOT, c s})) {x \<in> Te. \<exists>s. x = {ROOT, c s}}" 
    using  T.fin_edges unfolding w_red_def by (intro sum.inter_filter[symmetric])
  also have "... = sum (\<lambda>e. card (THE s. e = {ROOT, c s}))  {{ROOT, c s}|s. s \<in> S'}"
    using assms by (intro arg_cong[where ?f = "sum (\<lambda>e. card (THE s. e = {ROOT, c s}))"]) 
  also have "... = sum card ((\<lambda>e. THE s. e = {ROOT, c s}) ` {{ROOT, c s}|s. s \<in> S'})"
    by (subst o_def[of card, symmetric],intro sum.reindex[symmetric] inj_onI) 
      (force simp add: doubleton_eq_iff)
  also have  "... = sum card S'"
    by (intro sum.cong, subst Setcompr_eq_image, subst image_image)
       (auto simp add: doubleton_eq_iff)
  finally show ?thesis .
qed


definition COUNTER_EXAMPLE   where
  "COUNTER_EXAMPLE \<equiv> ({1::nat, 2 , 3}, {{1::nat,2}, {2,3}})"

lemma XC_to_steiner_tree_counterexample:
  shows  "XC_to_steiner_tree COUNTER_EXAMPLE \<in> steiner_tree"
       and "COUNTER_EXAMPLE \<notin> exact_cover"
proof
  define X where "X = {1::nat, 2 , 3}"
  define S where "S =  {{1::nat,2}, {2,3}}"
  show "XC_to_steiner_tree COUNTER_EXAMPLE \<in> steiner_tree"
  proof -
   
    let ?V = "(a ` X) \<union> {ROOT} \<union> (c ` S)"
    let ?E = "{{ROOT, c s} | s. s \<in> S} \<union> {{c s, a v} | s v. s \<in> S \<and> v \<in> s}"
    
    define Tv where "Tv = ?V"
    define Te where "Te = {{ROOT, c {1::nat,2}},
                           {c {1, 2}, a 1}, {c {1, 2}, a 2},
                           {c {2,3}, a 2}, {c {2,3}, a 3}}"
    have "fin_ulgraph ?V ?E" unfolding X_def S_def 
      by (unfold_locales, blast, fastforce, blast) 
 
    interpret T: fin_ulgraph Tv Te
      by(unfold_locales, unfold Tv_def Te_def S_def X_def, blast, force, blast)      

    have istree: "tree Tv Te"
    proof (intro card_E_treeI)
      show "card Tv = Suc (card Te)" 
      proof -
        have peel: " finite A \<Longrightarrow> x \<notin> A 
                    \<Longrightarrow> card A = (Suc k)  \<Longrightarrow> card (insert x A) = Suc (Suc k)" for x A k
          using card_insert_disjoint[of A x] by fastforce
        have peel2: "a \<noteq> b \<Longrightarrow> a \<notin> A2 \<Longrightarrow> a \<notin> (insert b A2)" for a b A2 
          by simp
        have "card Tv = 6" unfolding Tv_def X_def S_def
          by (code_simp)
        moreover have "card Te = Suc (Suc (Suc (Suc (Suc 0))))" unfolding Te_def 
          by (intro peel peel2) (auto simp add: doubleton_eq_iff)
        ultimately show ?thesis by auto
      qed

      have "T.vert_connected (a 2) (c {1, 2})"  using T.vert_connected_neighbors Te_def by blast
      moreover have "T.vert_connected (a 2) (c {2,3})" 
        using T.vert_connected_neighbors Te_def  by (simp add: insert_commute)

      ultimately have "T.vert_connected (a 2) v" if "v \<in> Tv" for v
        using that Tv_def Te_def X_def S_def T.vert_connected_neighbors[THEN T.vert_connected_trans[rotated]]
             by (simp add: doubleton_eq_iff) presburger
       

      then show "fin_connected_ulgraph Tv Te" using T.not_connected_set[of Tv "(a 2)" ] Tv_def
         T.vert_connected_wf
        by (unfold_locales,blast+) 
    qed
  moreover have "(\<Sum>e \<in> Te. w_red  e) \<le> card X"
  proof -
    have "{x \<in> Te. \<exists>s. x = {ROOT, c s}} = {{ROOT, c s} |s. s \<in> {{1, 2}}}"
      unfolding Te_def 
      by (simp,subst singleton_conv[symmetric, of "{ROOT, c {Suc 0, 2}}"],
           intro Collect_cong, blast) 
    then have h: "(\<Sum>e \<in> Te. w_red  e) = sum card {{1::nat, 2}}"
      using  total_w_is_sum_card[OF istree, of "{{1,2}}"] 
      by blast
    then show ?thesis unfolding X_def 
      by (subst h) fastforce
  qed
  moreover have "subgraph Tv Te ?V ?E"  using Tv_def Te_def X_def S_def
     by (unfold_locales) blast+
 
  ultimately have "(?V, ?E, w_red,{ROOT} \<union> (a ` X), card X) \<in> steiner_tree" using Tv_def
    by (intro steiner_tree_cert[OF istree \<open>fin_ulgraph ?V ?E\<close>]) auto  
  thus ?thesis unfolding XC_to_steiner_tree_def COUNTER_EXAMPLE_def  S_def X_def by fast
qed
  show "steiner_tree \<subseteq> steiner_tree" by auto
  show "COUNTER_EXAMPLE \<notin> exact_cover" 
  proof (rule ccontr)
    assume "\<not>(COUNTER_EXAMPLE \<notin> exact_cover)"
    then have "(X,S) \<in> exact_cover" using X_def COUNTER_EXAMPLE_def S_def by auto
    then obtain S' where
    "finite X" "\<Union>S \<subseteq> X" "S' \<subseteq> S" "\<Union>S' = X" "pairwise disjnt S'"
    unfolding exact_cover_def by blast
    then have "S' \<in> {{}, {{1,2}}, {{2,3}}, {{1,2},{2,3}}}"
      unfolding S_def  by blast
    then consider
      (empty)"S' = {}" |
      (one12) "S' = {{1,2}}" |
      (one23) "S' = {{2,3}}" |
      (both) "S' = {{1,2},{2,3}}"
      by blast
    then show False 
    proof (cases)
      case empty
      then show ?thesis using \<open>\<Union>S' = X\<close> X_def by blast
    next
      case one12
      then have "\<Union>S' = {1,2}"  by auto
      then show ?thesis using \<open>\<Union>S' = X\<close> unfolding X_def by auto
    next
      case one23
      then have eq: "X = {2,3}" using \<open>\<Union>S' = X\<close> by auto
      then show ?thesis unfolding X_def by fastforce
    next
      case both
      then have "pairwise disjnt {{1::nat,2},{2,3}}" using \<open>pairwise disjnt S'\<close>  by blast
      then show ?thesis by (simp add: doubleton_eq_iff pairwise_insert)
    qed
 
   qed 
 qed   


theorem is_not_reduction_XC_to_steiner_tree:
  "\<not>is_reduction XC_to_steiner_tree exact_cover steiner_tree"
proof
  assume "is_reduction XC_to_steiner_tree exact_cover steiner_tree"
  then have reduction_property: "\<forall>a. (a \<in> exact_cover) = (XC_to_steiner_tree a \<in> steiner_tree)"
    unfolding is_reduction_def sorry (* why ? *)
  then show False using XC_to_steiner_tree_counterexample  by blast
qed



end