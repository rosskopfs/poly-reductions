theory XC_To_ST
  imports Undirected_Graph_Theory.Undirected_Graphs_Root 
          Tree_Enumeration.Tree_Graph
           "../SAT_To_XC/XC_Definition"
begin


(* Definition of the Steiner Tree problem *)

type_synonym 'a steiner_tree_tuple = "('a set \<times> 'a edge set \<times> ('a edge \<Rightarrow> nat) \<times> 'a set \<times> nat)" 
definition steiner_tree :: "'a steiner_tree_tuple set" where
  "steiner_tree \<equiv> 
    { (V, E, w, R, k). fin_ulgraph V E \<and> R \<subseteq> V \<and>
      (\<exists> Tv Te. tree Tv Te  \<and> subgraph Tv Te V E \<and> R \<subseteq> Tv \<and> (\<Sum>e \<in> Te. w e) \<le> k) }"


lemma steiner_tree_cert:
  assumes "tree Tv Te"
          "fin_ulgraph V E"
          "R \<subseteq> V"
          "subgraph Tv Te V E"
          "R \<subseteq> Tv"
          "(\<Sum>e \<in> Te. w e) \<le> k"
  shows "(V, E, w, R, k) \<in> steiner_tree"
  using assms steiner_tree_def by fastforce

(* reduction *)

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

(* helper lemma *)
lemma disjoint_if_sum_card_eq_card:
  assumes "finite (\<Union>S)"
          "sum card S = card (\<Union>S)"
        shows "disjoint S"
proof (intro Disjoint_Sets.disjointI)
  fix a assume "a \<in> S"
  fix b assume "b \<in> S"
  assume neq: "a \<noteq> b"
  show "a \<inter> b = {}"
  proof (rule ccontr)
    assume "a \<inter> b \<noteq> {}"
    have "finite a" and "finite b"
      by (meson Union_upper \<open>a \<in> S\<close> \<open>b \<in> S\<close>  assms(1) finite_subset)+
    have caub: "card(a \<union> b) < card a + card b"
      using \<open>a \<inter> b \<noteq> {}\<close> \<open>finite a\<close> \<open>finite b\<close> card_Un_Int by fastforce
    have *: "sum card S = sum card (S- {a,b}) + sum card {a, b}"
      by (simp add: \<open>a \<in> S\<close> \<open>b \<in> S\<close> assms(1) finite_UnionD sum.subset_diff)
    have "card (\<Union>S) \<le> card (\<Union>(S - {a,b}) \<union> (a \<union> b))" using \<open>a \<in> S\<close> \<open>b \<in> S\<close>
      by (intro arg_cong[THEN eq_imp_le, where ?f1 = card],blast)
   also have  "...   \<le>  sum card (S- {a,b}) + card(a \<union> b)"
      using add_le_mono1 card_Union_le_sum_card card_Un_le order_trans by meson
    also have "...  < sum card (S- {a,b})  +  card a + card b" 
      using caub by linarith
    finally show False  using "*"  assms by (simp add: neq)
  qed
qed

lemma XC_to_steiner_tree_sound:
  assumes "(X, S) \<in> exact_cover"
  shows "XC_to_steiner_tree (X, S) \<in> steiner_tree"
proof -
  from assms obtain S' where
    "finite X" "\<Union>S \<subseteq> X" "S' \<subseteq> S" "\<Union>S' = X" "pairwise disjnt S'"
    unfolding exact_cover_def by blast

  let ?V = "(a ` X) \<union> {ROOT} \<union> (c ` S)"
  let ?E = "{{ROOT, c s} | s. s \<in> S} \<union> {{c s, a v} | s v. s \<in> S \<and> v \<in> s}"
  let ?R = "{ROOT} \<union> (a ` X)"
  let ?k = "card X"

  have fS: "finite S'"
    by (simp add: \<open>\<Union> S' = X\<close> \<open>finite X\<close> finite_UnionD)
  have f: "finite s" if "s \<in> S'" for s
    using \<open>\<Union>S' = X\<close> \<open>finite X\<close> that rev_finite_subset by blast
  have "finite S"  using \<open>\<Union> S \<subseteq> X\<close>  finite_subset \<open>finite X\<close>   
    by (intro finite_UnionD) blast
  then have "finite ?V" using \<open>finite X\<close> by fast 
  then have "fin_ulgraph ?V ?E" using \<open>\<Union> S \<subseteq> X\<close>  by (unfold_locales) auto
  define Tv where "Tv = ?R \<union> (c ` S')"
  define Te where "Te = {{ROOT, c s} | s. s \<in> S'} \<union> {{c s, a v} | s v. s \<in> S' \<and> v \<in> s}"

  have sum_card_S': "sum card S'= card X" 
    using \<open>\<Union> S' = X\<close> \<open>disjoint S'\<close> card_Union_disjoint f  by fastforce
     
  interpret T: fin_ulgraph Tv Te
      by (unfold_locales, unfold Tv_def Te_def ) 
         (use \<open>\<Union> S \<subseteq> X\<close>  finite_subset[of S' S]  \<open>S' \<subseteq> S\<close>
              \<open>finite X\<close> \<open>finite S\<close>  in auto)  

  have istree: "tree Tv Te"
  proof (intro card_E_treeI)
    show "card Tv = Suc (card Te)" 
    proof -
      have dis: "disjoint {{{c s, a v} | v. v \<in> s} |s. s \<in> S'}"
        unfolding disjoint_def by (auto simp add: doubleton_eq_iff)
      have  "card {{c s, a v} |s v. s \<in> S' \<and> v \<in> s} =
             card  ( \<Union>  {{{c s, a v} | v. v \<in> s} |s. s \<in> S'})"
        by (intro arg_cong[where ?f = "card"]) auto
      also have "... = sum card ((\<lambda>s. {{c s, a v} | v. v \<in> s})  ` S')"
        using f card_Union_disjoint[OF dis] by (auto simp add: Setcompr_eq_image)
      also have "... = sum card S'"
      proof - 
        have inj: "inj_on (\<lambda>s. {{c s, a v} | v. v \<in> s}) S'" 
        proof (intro inj_onCI)
          fix x assume "x \<in> S'"
          fix y assume "y \<in> S'"
          assume eq: "{{c x, a v} |v. v \<in> x} = {{c y, a v} |v. v \<in> y}"
          assume "x \<noteq> y"
          moreover obtain s where s_def: "s \<in> {{c x, a v} |v. v \<in> x}" using eq \<open>x \<noteq> y\<close> by fastforce
          moreover then obtain u where "s = {c x, a u}" by blast
          moreover obtain v where "s = {c y, a v}" using eq s_def by blast
          ultimately show False  by (simp add: doubleton_eq_iff)
        qed  
        show ?thesis 
          by (subst sum.reindex[OF inj], intro sum.cong)
             (auto simp add: Setcompr_eq_image[of "(\<lambda>v. {c s, a v})" for s]
                             card_image doubleton_eq_iff inj_on_def)
      qed
      finally have "card Te = card {{ROOT, c s} | s. s \<in> S'} + card X"
        using T.fin_edges Te_def card_Un_disjoint[where ?B = "{{c s, a v} |s v. s \<in> S' \<and> v \<in> s}"]
        sum_card_S' by auto
      moreover have "card {{ROOT, c s} | s. s \<in> S'} = card S'"
        by (subst Setcompr_eq_image[of "\<lambda>s. {ROOT, c s}"],
            auto simp add: doubleton_eq_iff inj_on_def card_image)
      ultimately have "card Te = card S' + card X"   by presburger
      moreover have "card Tv = Suc(card (a ` X \<union> c ` S'))"
        unfolding Tv_def  by (simp add: \<open>finite X\<close> fS image_iff)
      moreover have "card (a ` X \<union> c ` S') =  card X + card  S'"
        by (simp add: \<open>\<Union> S' = X\<close> \<open>finite X\<close> card_Un_disjnt disjnt_def disjoint_iff_not_equal 
                      finite_UnionD,
            intro Groups.add_mono_thms_linordered_semiring(4),
            meson card_image inj_onI red_vertex.inject)
      ultimately show ?thesis  by presburger
    qed
    
    have "T.vert_connected ROOT v" if "v \<in> Tv" for v
    proof (cases v)
      case ROOT
      then show ?thesis  using T.vert_connected_id that by blast
    next
      case (c s)
      then show ?thesis  using that Tv_def Te_def 
        by(intro T.vert_connected_neighbors) blast 
    next
      case (a x) 
      have "x \<in> X" using that by (simp add: Tv_def a image_iff)
      then obtain s where "s \<in> S'" and "T.vert_connected (c s) (a x)"
        using \<open>\<Union>S' = X\<close> UnionE T.vert_connected_neighbors Te_def by blast
      then show ?thesis  using T.vert_connected_neighbors T.vert_connected_trans Te_def a
        by blast
    qed
    then show "fin_connected_ulgraph Tv Te" using T.not_connected_set[of Tv ROOT] Tv_def
      by (unfold_locales) auto
  qed
  
  moreover have "(\<Sum>e \<in> Te. w_red  e) \<le> ?k"
    using sum_card_S' total_w_is_sum_card istree Te_def
    by (subst sum_card_S'[symmetric],        
        intro total_w_is_sum_card[THEN eq_imp_le], auto)
  moreover have "subgraph Tv Te ?V ?E"  using \<open>\<Union> S \<subseteq> X\<close> \<open>S' \<subseteq> S\<close>
    by (unfold_locales, unfold Tv_def Te_def, fastforce+)
  ultimately have "(?V, ?E, w_red, ?R, ?k) \<in> steiner_tree" using Tv_def
    by (intro steiner_tree_cert[OF istree \<open>fin_ulgraph ?V ?E\<close>]) auto  
  thus ?thesis unfolding XC_to_steiner_tree_def  by fast
qed


lemma XC_to_steiner_tree_complete:
  assumes "XC_to_steiner_tree (X, S) \<in> steiner_tree"
  shows "(X, S) \<in> exact_cover"
proof -
  let ?V = "(a ` X) \<union> {ROOT} \<union> (c ` S)"
  let ?E = "{{ROOT, c s} | s. s \<in> S} \<union> {{c s, a v} | s v. s \<in> S \<and> v \<in> s}"
  let ?R = "{ROOT} \<union> (a ` X)"
  let ?k = "card X"

  obtain Tv Te where
    "tree Tv Te" "subgraph Tv Te ?V ?E" "?R \<subseteq> Tv" "(\<Sum>e \<in> Te. w_red e) \<le> ?k"
    using assms unfolding XC_to_steiner_tree_def steiner_tree_def by auto
  define S' where "S' = {s \<in> S. {c s, ROOT} \<in> Te}" 
  (* proof was hader if we define it as {s \<in> S. c s \<in> Tv} *)

  interpret G: fin_ulgraph ?V ?E  using assms
    unfolding XC_to_steiner_tree_def steiner_tree_def
    by fastforce
  interpret T: tree Tv Te  using \<open>tree Tv Te\<close> by blast
  interpret sub: subgraph Tv Te ?V ?E using \<open>subgraph Tv Te ?V ?E\<close> by blast

  have "finite X"
    by (rule finite_image_iff[of a, THEN iffD1],
             meson inj_onI red_vertex.inject,
             use G.finV in blast)
  have "\<Union>S \<subseteq> X"
  proof (intro subsetI)
    fix x assume "x \<in> \<Union> S"
    then obtain s where "x \<in> s" "s \<in> S" by force 
    then have "{c s,  a x} \<in> ?E" by blast
    then show "x \<in> X"  using G.wellformed_alt_snd by blast
  qed

  have "\<Union>S' = X"
  proof
    show "\<Union>S' \<subseteq> X"  using S'_def \<open>\<Union> S \<subseteq> X\<close> by blast
    show "X \<subseteq> \<Union>S'"
    proof
      fix x assume "x \<in> X"
      then have "a x \<in> Tv" and "ROOT \<in> Tv" using \<open>?R \<subseteq> Tv\<close> by auto
      moreover then have T.non_trivial using T.non_trivial_def T.V_E_empty 
          T.card_V_card_E T.fin_edges not_less_eq_eq by fastforce
      (* is this true? *)
      ultimately show "x \<in> \<Union>S'" sorry
    qed
  qed

  have "{x \<in> Te. \<exists>s. x = {ROOT, c s}} = {{ROOT, c s}|s. s \<in> S'}" 
  proof 
    show "{x \<in> Te. \<exists>s. x = {ROOT, c s}} \<subseteq> {{ROOT, c s}|s. s \<in> S'}" 
    proof
      fix x assume "x \<in> {x \<in> Te. \<exists>s. x = {ROOT, c s}}"
      then obtain s where "x = {ROOT, c s}" and "s \<in> S"  and "x \<in> Te" using sub.edges_ss by blast
      moreover then have "s \<in> S'" by (simp add: S'_def insert_commute)
      ultimately show "x \<in> {{ROOT, c s}|s. s \<in> S'}" by blast
    qed
    show "{{ROOT, c s}|s. s \<in> S'} \<subseteq> {x \<in> Te. \<exists>s. x = {ROOT, c s}}" 
    proof 
      fix x assume "x \<in> {{ROOT, c s}|s. s \<in> S'}"
      then obtain s where "x = {ROOT, c s}"  and "s \<in> S'"  by blast
      moreover then have "x \<in> Te" unfolding S'_def  by (simp add: insert_commute)
      ultimately show "x \<in> {x \<in> Te. \<exists>s. x = {ROOT, c s}}" by blast
    qed
  qed
  then have "sum card S'\<le> card (\<Union>S')" 
    using total_w_is_sum_card[OF\<open>tree Tv Te\<close>, of S'] \<open>(\<Sum>e \<in> Te. w_red e) \<le> ?k\<close>  \<open>\<Union>S' = X\<close> 
    by presburger
  moreover have "\<Union>S' \<subseteq> X"  using S'_def \<open>\<Union> S \<subseteq> X\<close> by blast
  ultimately have "disjoint S'"  
    using \<open>\<Union> S' = X\<close> \<open>finite X\<close> antisym card_Union_le_sum_card  disjoint_if_sum_card_eq_card
    by blast
  thus ?thesis sorry
qed


end