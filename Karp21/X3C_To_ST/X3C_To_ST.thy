theory X3C_To_ST
  imports ST_Definition "Reductions" 
          "Poly_Reductions_Lib.Discriminated_Union"
          "X3C_Definition" 
          "Poly_Reductions_Lib.Set_Auxiliaries" (* card_Collect_mem *)
begin

(* reduction *)
datatype 'a red_vertex = a 'a | ROOT |  c "'a set"

definition NOT_STEINER_TREE_EXAMPLE :: "('a red_vertex) steiner_tree_tuple" where
  "NOT_STEINER_TREE_EXAMPLE \<equiv> ({},{}, \<lambda>e. 1,{ROOT},0)"

(*  Alessandro Santuari 2003  *)
definition X3C_to_steiner_tree ::
    "'a set \<times> 'a set set  \<Rightarrow> ('a red_vertex) steiner_tree_tuple " where
   "X3C_to_steiner_tree \<equiv> \<lambda>(X, S). if (\<forall>C \<in> S. card C = 3) then
   ( (a ` X) \<union> {ROOT} \<union> (c ` S),
     {{ROOT, c s} | s. s \<in> S} \<union> {{c u, a v} | u v. u \<in> S \<and> v \<in> u}, \<lambda>e. 1,
     {ROOT} \<union>  (a ` X),
    4 * card X div 3) else NOT_STEINER_TREE_EXAMPLE"

lemma example_not_in_steiner_tree:
  "NOT_STEINER_TREE_EXAMPLE \<notin> steiner_tree"
  unfolding NOT_STEINER_TREE_EXAMPLE_def 
proof (rule ccontr)
  assume "\<not> ({}, {}, \<lambda>e. 1, {ROOT::'a red_vertex}, 0) \<notin> steiner_tree"
  then obtain Tv Te  where "subgraph Tv Te {} {}" "{ROOT::'a red_vertex}  \<subseteq> Tv"  
    unfolding steiner_tree_def by blast
  then show False using subgraph.verts_ss by fast
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
    also have "...  < sum card (S- {a,b}) + card a + card b" 
      using caub by linarith
    finally show False  using "*"  assms by (simp add: neq)
  qed
qed


lemma card_red_V:
  assumes "finite X" "finite S"
  shows "card ({ROOT} \<union> (a ` X)  \<union> (c ` S)) = Suc(card X + card S)"
proof -
  have "card (a ` X \<union> c ` S) = card (a ` X) + card (c ` S)"
    by (simp add: assms card_Un_disjoint disjoint_iff_not_equal)  
  also have "... = card X + card  S"
    by (intro Groups.add_mono_thms_linordered_semiring)
       (meson card_image inj_onI red_vertex.inject)
  finally have "card (a ` X \<union> c ` S) = card X + card  S".
  then show ?thesis  by (simp add: assms image_iff)
qed

 

lemma X3C_to_steiner_tree_sound:
  assumes "(X, S) \<in> three_exact_cover"
  shows "X3C_to_steiner_tree (X, S) \<in> steiner_tree"
proof -
  from assms obtain S' where
    "finite X" "\<Union>S \<subseteq> X" "S' \<subseteq> S" "\<Union>S' = X" "pairwise disjnt S'" "(\<forall>C \<in> S. card C = 3)"
    unfolding three_exact_cover_def by blast

  let ?V = "{ROOT} \<union> (a ` X) \<union> (c ` S)"
  let ?E = "{{ROOT, c s} | s. s \<in> S} \<union> {{c s, a v} | s v. s \<in> S \<and> v \<in> s}"
  let ?R = "{ROOT} \<union> (a ` X)"
  let ?k = "4 * card X div 3"
  let ?w = "\<lambda>i. 1::nat"

  have finS': "finite S'"
    by (simp add: \<open>\<Union> S' = X\<close> \<open>finite X\<close> finite_UnionD)
  have fin_s': "(\<And>s. s \<in> S' \<Longrightarrow> finite s)"
    using \<open>\<Union>S' = X\<close> \<open>finite X\<close> rev_finite_subset by blast
  have "finite S"  using \<open>\<Union> S \<subseteq> X\<close>  finite_subset \<open>finite X\<close>   
    by (intro finite_UnionD) blast
  then have "finite ?V" using \<open>finite X\<close> by fast 
  then have "fin_ulgraph ?V ?E" using \<open>\<Union> S \<subseteq> X\<close>  by (unfold_locales) auto
  define Tv where "Tv = ?R \<union> (c ` S')"
  define Te where "Te = {{ROOT, c s} | s. s \<in> S'} \<union> {{c s, a v} | s v. s \<in> S' \<and> v \<in> s}"

  have sum_card_S': "sum card S'= card X" 
    using \<open>\<Union> S' = X\<close> \<open>disjoint S'\<close> card_Union_disjoint fin_s' 
    by fastforce
     
  interpret T: fin_ulgraph Tv Te
      by (unfold_locales, unfold Tv_def Te_def ) 
         (use \<open>\<Union> S \<subseteq> X\<close>  finite_subset[of S' S]  \<open>S' \<subseteq> S\<close>
              \<open>finite X\<close> \<open>finite S\<close>  in auto)  

  have card_Te:"card Te = card S' + card X "
  proof -
    have "card Te = card {{ROOT, c s} | s. s \<in> S'} + 
                    card {{c s, a v} |s v. s \<in> S' \<and> v \<in> s}"
      using T.fin_edges Te_def card_Un_disjoint by blast
    moreover {     
      have "{{c s, a v} |s v. s \<in> S' \<and> v \<in> s}
            = (\<lambda>(v,s). {c s, a v}) ` (\<Uplus>S')"
        by auto
      moreover have "inj_on (\<lambda>(v,s). {c s, a v }) (\<Uplus>S')"
        by (simp add: doubleton_eq_iff inj_on_def)
      ultimately have "card {{c s, a v} |s v. s \<in> S' \<and> v \<in> s}  = sum card S'"
        using card_discriminated_Union[OF fin_s'] card_image
        by fastforce
      then have "card {{c s, a v} |s v. s \<in> S' \<and> v \<in> s} = card X"
        using sum_card_S' by presburger
    }
    moreover have "card {{ROOT, c s} | s. s \<in> S'} =  card S'"
        by (intro card_Collect_mem) (simp add: doubleton_eq_iff inj_on_def)
    ultimately show "card Te = card S' + card X" by presburger
  qed

  have istree: "tree Tv Te"
  proof (intro card_E_treeI)
    show "card Tv = Suc (card Te)" 
      using card_red_V[OF \<open>finite X\<close> finS'] card_Te Tv_def 
      by presburger
    
    have "T.vert_connected ROOT v" if "v \<in> Tv" for v
    proof (cases v)
      case ROOT
      then show ?thesis using T.vert_connected_id that by blast
    next
      case (c s)
      then show ?thesis using that Tv_def Te_def 
        by(intro T.vert_connected_neighbors) blast 
    next
      case (a x) 
      have "x \<in> X" using that by (simp add: Tv_def a image_iff)
      then obtain s where "s \<in> S'" and "T.vert_connected (c s) (a x)"
        using \<open>\<Union>S' = X\<close> UnionE T.vert_connected_neighbors Te_def by blast
      then show ?thesis 
        using T.vert_connected_neighbors T.vert_connected_trans Te_def a by blast
    qed
    then show "fin_connected_ulgraph Tv Te" using T.not_connected_set[of Tv ROOT] Tv_def
      by (unfold_locales) auto
  qed
  
  moreover have "(\<Sum>e \<in> Te. ?w  e) \<le> ?k"
  proof -
    have "\<forall>C\<in>S'. card C = 3" using \<open>S' \<subseteq> S\<close> \<open>\<forall>C\<in>S. card C = 3\<close> by blast
    then have "sum card S' = 3 * card S'" by force
    moreover have "(\<Sum>e \<in> Te. ?w  e) = card Te"  by fastforce
    ultimately show ?thesis using card_Te sum_card_S' by auto
  qed
   
  moreover have "subgraph Tv Te ?V ?E"  using \<open>\<Union> S \<subseteq> X\<close> \<open>S' \<subseteq> S\<close>
    by (unfold_locales, unfold Tv_def Te_def, fastforce+)
  ultimately have "(?V, ?E, ?w, ?R, ?k) \<in> steiner_tree" using Tv_def
    by (intro steiner_tree_cert[OF istree \<open>fin_ulgraph ?V ?E\<close>]) auto  
  thus ?thesis unfolding X3C_to_steiner_tree_def using \<open>\<forall>C\<in>S. card C = 3\<close> by fastforce
qed


lemma X3C_to_steiner_tree_complete:
  assumes "X3C_to_steiner_tree (X, S) \<in> steiner_tree"
  shows "(X, S) \<in> three_exact_cover"
proof (cases "\<forall>C\<in>S. card C = 3")
  case True
   let ?V = "{ROOT} \<union> (a ` X) \<union> (c ` S)"
   let ?E = "{{ROOT, c s} | s. s \<in> S} \<union> {{c s, a v} | s v. s \<in> S \<and> v \<in> s}"
   let ?R = "{ROOT} \<union> (a ` X)"
   let ?k = "4 * card X div 3"
   let ?w = "\<lambda>e. 1"
   obtain Tv Te where
     "tree Tv Te" "subgraph Tv Te ?V ?E" "?R \<subseteq> Tv" "(\<Sum>e \<in> Te. ?w e) \<le> ?k"
     using assms unfolding X3C_to_steiner_tree_def steiner_tree_def using True by auto
   define S' where "S' = {s \<in> S. c s \<in> Tv}" 
   interpret G: fin_ulgraph ?V ?E  using assms True
     unfolding X3C_to_steiner_tree_def steiner_tree_def by simp
   interpret T: tree Tv Te  using \<open>tree Tv Te\<close> by blast
   interpret sub: subgraph Tv Te ?V ?E using \<open>subgraph Tv Te ?V ?E\<close> by blast
   show ?thesis 
   proof (intro three_exact_cover_cert[of S'])
     show "finite X"
       by (rule finite_image_iff[of a, THEN iffD1],
           meson inj_onI red_vertex.inject,
           use G.finV in blast)
     show "\<forall>C\<in>S. card C = 3" using True.
     show "S' \<subseteq> S" using S'_def by simp
     show "\<Union>S \<subseteq> X"
     proof (intro subsetI)
       fix x assume "x \<in> \<Union> S"
       then obtain s where "x \<in> s" "s \<in> S" by force 
       then have "{c s,  a x} \<in> ?E" by blast
       then show "x \<in> X"  using G.wellformed_alt_snd by blast
     qed

     have "\<Union>S' \<subseteq> X"  using S'_def \<open>\<Union> S \<subseteq> X\<close> by blast 
     moreover have "X \<subseteq> \<Union> S'"
     proof(intro subsetI)
       fix x assume "x \<in> X"
       have "a x \<in> Tv"    
         using \<open>x \<in> X\<close> \<open>{ROOT} \<union> a ` X \<subseteq> Tv\<close> by auto
       moreover have "ROOT \<in> Tv" using \<open>?R \<subseteq> Tv\<close> by auto
       ultimately have T.non_trivial 
         using T.V_E_empty T.card_V_card_E T.fin_edges T.non_trivial_def not_less_eq_eq
         by force
       then obtain e where "a x  \<in> e" "e \<in> Te" 
         using T.V_Union_E  \<open>a x \<in> Tv\<close> by blast
       then have "e \<in> ?E" using sub.edges_ss   by blast
       then obtain s where "s \<in> S" "e = {c s, a x}" "x \<in> s"
         using \<open>a x \<in> e\<close> by blast
       then have "c s \<in> Tv" 
         using T.wellformed_alt_fst \<open>e \<in> Te\<close> by blast
       then have "s \<in> S'" using S'_def \<open>s \<in> S\<close> by auto
       thus "x \<in> \<Union>S'"  using \<open>x \<in> s\<close> by blast
     qed
     ultimately show "\<Union> S' = X"  by blast


     have "card Te \<le> 4 * card X div 3" 
       using \<open>(\<Sum>e \<in> Te. ?w e) \<le> ?k\<close>  by force
     then have "card Tv \<le> Suc(4 * card X div 3)" 
       using Suc_le_mono T.card_V_card_E by presburger
     moreover {
       have "finite S'"
         by (simp add: \<open>\<Union> S' = X\<close> \<open>finite X\<close> finite_UnionD)
       have "Tv = ?R \<union> c ` S'" 
         using sub.verts_ss \<open>?R\<subseteq>Tv\<close> S'_def by auto
       then have "card Tv = Suc (card X + card S')" 
         using \<open>finite S'\<close> \<open>finite X\<close> card_red_V by blast
     }
     ultimately have "card S' \<le> card X div 3" by fastforce
     moreover have "\<forall>C\<in>S'. card C = 3" using S'_def True by blast
     ultimately have "sum card S' = card (\<Union> S')" 
       using card_Union_le_sum_card \<open>\<Union> S' = X\<close>
       by (intro le_antisym) (force, fast)
     then show "disjoint S'" 
       using disjoint_if_sum_card_eq_card using \<open>\<Union> S' = X\<close> \<open>finite X\<close>
       by blast
  qed  
  next
    case False
    then have "X3C_to_steiner_tree (X, S) = NOT_STEINER_TREE_EXAMPLE" 
      unfolding X3C_to_steiner_tree_def by auto
    then show ?thesis
      using example_not_in_steiner_tree assms by auto
qed

theorem is_reduction_X3C_to_steiner_tree:
  "is_reduction X3C_to_steiner_tree three_exact_cover steiner_tree"
  unfolding is_reduction_def 
  using X3C_to_steiner_tree_sound X3C_to_steiner_tree_complete
  by auto

end
