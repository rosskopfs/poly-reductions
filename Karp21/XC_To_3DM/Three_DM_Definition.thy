theory Three_DM_Definition
  imports "HOL-Library.Disjoint_Sets"  "../Reductions"  "../../Lib/Auxiliaries/Set_Auxiliaries"
begin

section \<open>Triplets with distinct components\<close>

text "A property that a 3d matching must meet:
      if two triplets share the same component then they must be the same
      * two points from M1 and M2 do not from lines parallel to the grid axes)"

definition distinct_components3 where
 "distinct_components3 M1 M2 = (\<forall>(a, b, c) \<in> M1. 
                    \<forall>(a1, b1, c1) \<in> M2. 
                     (a = a1 \<or> b = b1 \<or> c = c1) \<longrightarrow> (a, b, c) = (a1, b1, c1))"

abbreviation self_distinct_components3 where
 "self_distinct_components3  M \<equiv> distinct_components3 M M "

lemma self_distinct_components3_injI:
  assumes "inj_on f S"
          "inj_on g S"
          "inj_on h S"
  shows "self_distinct_components3 {(f x, g x, h x)|x. x \<in> S}"
  using assms unfolding inj_on_def distinct_components3_def
  by blast

lemma self_distinct_components3_unionI:
  assumes "self_distinct_components3 M1"
          "self_distinct_components3 M2"
          "distinct_components3 M1 M2"       
  shows "self_distinct_components3 (M1 \<union> M2)"
  using assms unfolding distinct_components3_def
  by auto

lemma self_distinct_components3_subset:
  assumes "self_distinct_components3 B"
          "A \<subseteq> B"
  shows "self_distinct_components3 A"
  using assms in_mono
  unfolding distinct_components3_def
  by fast

lemma distinct_components3I:
  assumes "\<And> a b c a1 b1 c1.
            (a,b,c) \<in> M1 \<Longrightarrow>
            (a1,b1,c1) \<in> M2 \<Longrightarrow>
            (a=a1 \<or> b=b1 \<or> c=c1) \<Longrightarrow> ((a,b,c) = (a1,b1,c1))"
  shows "distinct_components3  M1 M2"
  using assms unfolding distinct_components3_def
  by blast
        
section \<open>Karp72 Definition\<close>

definition "three_d_matching \<equiv> 
    {(U, T). U \<subseteq> (T \<times> T \<times> T) \<and> finite T \<and>
     (\<exists>M \<subseteq> U.  (card M = card T) \<and> self_distinct_components3 M)}"


lemma three_d_matching_cert:
  assumes "M \<subseteq> U"
          "card M = card T"
          "U \<subseteq> (T \<times> T \<times> T)"
          "finite T"
          "self_distinct_components3 M"
  shows "(U,T) \<in> three_d_matching"
  unfolding three_d_matching_def using assms
  by blast

text "these lemmas show each column of the matching covers T"

lemma fM_T:
  assumes  "f ` M  \<subseteq> T" 
           "inj_on f M"
           "card M = card T" 
           "finite T"
  shows "f ` M = T"
proof -
   have "card (f ` M) = card T" 
     using  \<open>card M = card T\<close> \<open>inj_on f M\<close>
     by (intro card_image[THEN trans])
   then show ?thesis 
     by (simp add: \<open>finite T\<close> card_subset_eq \<open>f ` M  \<subseteq> T\<close>)
qed

lemma fstM_T:
  assumes  "M \<subseteq>  T \<times> T \<times> T" 
           "card M = card T" 
           "self_distinct_components3 M" 
           "finite T"
  shows "fst ` M = T"
  using assms distinct_components3_def
  by (intro fM_T) (auto simp add: inj_on_def, fast+)

abbreviation t3_snd where  "t3_snd \<equiv> fst \<circ> snd"
lemma sndM_T:
  assumes  "M \<subseteq>  T \<times> T \<times> T" 
           "card M = card T" 
           "self_distinct_components3 M" 
           "finite T"
  shows "t3_snd ` M = T"
  using assms distinct_components3_def
  by (intro fM_T) (auto simp add: inj_on_def, fast+)

abbreviation t3_thrd where  "t3_thrd \<equiv> snd \<circ> snd"
 
lemma thrdM_T:
  assumes  "M \<subseteq>  T \<times> T \<times> T" 
           "card M = card T" 
           "self_distinct_components3 M" 
           "finite T"
  shows "t3_thrd ` M = T"
  using assms distinct_components3_def
  by (intro fM_T) (auto simp add: inj_on_def, fast+)

section \<open>Alternative Definitions\<close>


text "used by Computers and Intractability (Michael R. Garey and David S. Johnson) p.46" 
    
definition "three_d_matching_alt1 \<equiv>
    {(M, X, Y, Z). M \<subseteq> (X \<times> Y \<times> Z) 
                  \<and> finite X \<and> finite Y \<and> finite Z 
                  \<and> disjoint {X, Y, Z} 
                  \<and> (card X = card Y) \<and> (card X = card Z) \<and>
     (\<exists>M' \<subseteq> M.  (card M' = card X) \<and> self_distinct_components3 M')}"



definition three_dm_to_alt1 where
  "three_dm_to_alt1  \<equiv> (\<lambda>(U,T).
     let X = {(t, 0::nat) | t. t \<in> T};
         Y = {(t, 1::nat) | t. t \<in> T};
         Z = {(t, 2::nat) | t. t \<in> T};
         M = { ((a, 0::nat), (b, 1::nat), (c, 2::nat)) | a b c. (a,b,c) \<in> U }
     in (M, X, Y, Z))"



lemma card_tagged:
  "card {(x,k)|x. x \<in> P} = card P"
  by (intro card_Collect_mem) 
     (simp add: inj_on_convol_ident)


lemma three_d_matching_to_alt1_sound:
  assumes "(U, T) \<in> three_d_matching"
  shows "(three_dm_to_alt1 (U,T)) \<in> three_d_matching_alt1"
proof -
  obtain M where "M \<subseteq> U"  "card M = card T" "self_distinct_components3 M"
    using assms unfolding three_d_matching_def 
    by blast
  let ?M'  = "{((a, 0::nat), (b, Suc 0), (c, 2::nat)) |a b c. (a, b, c) \<in> M}"
  have "?M' \<subseteq> {((a, 0::nat), (b, Suc 0), (c, 2::nat)) |a b c. (a, b, c) \<in> U}"
    using \<open>M \<subseteq> U\<close>  by blast
  moreover{ 
    have *:"inj_on (\<lambda>(a, b, c). ((a, 0), (b, Suc 0), c, 2)) M"
      unfolding inj_on_def by auto
    have "card ?M' = card M"
      using card_Collect_mem[OF *] by simp   
  }  
  moreover have "self_distinct_components3 ?M'"
    using \<open>self_distinct_components3 M\<close>
    unfolding distinct_components3_def by auto
  ultimately show ?thesis
    using assms \<open>card M = card T\<close> 
    unfolding three_d_matching_def three_d_matching_alt1_def
              three_dm_to_alt1_def Let_def disjoint_def
    by (auto simp add: card_tagged)
qed
    

lemma three_d_matching_to_alt1_complete:
  assumes "three_dm_to_alt1 (U,T) \<in> three_d_matching_alt1"
  shows "(U, T) \<in> three_d_matching"
proof -
  obtain M' where M'_def: "M' \<subseteq> {((a, 0::nat), (b, Suc 0), (c, 2::nat)) |a b c. (a, b, c) \<in> U}" 
    "card M' = card T" "self_distinct_components3 M'"
    using assms unfolding three_d_matching_alt1_def three_dm_to_alt1_def
    by (auto simp add:card_tagged)
  define M where " M = (\<lambda>(a,b,c). (fst a, fst b, fst c)) ` M'"
  have "M \<subseteq> U" 
    using M_def M'_def  by force
  moreover have "card M = card M'" 
    using M'_def unfolding M_def
    by (intro card_image) (auto simp add: inj_on_def)
  moreover {
    have *: "M' = {((a, 0::nat), (b, Suc 0), (c, 2::nat)) |a b c. (a, b, c) \<in> M}"
      using M'_def unfolding M_def by force
    then have "self_distinct_components3 M"
      using \<open>self_distinct_components3 M'\<close>
      unfolding distinct_components3_def
      by (auto simp add: * )
  }    
  ultimately show ?thesis
    using assms \<open>card M' = card T\<close> 
    unfolding three_d_matching_def three_d_matching_alt1_def
              three_dm_to_alt1_def Let_def 
    [[simproc add: finite_Collect]]
    by (auto simp add: inj_on_def finite_image_iff, blast+)
qed

theorem is_reduction_3dm_to_alt1:
  "is_reduction three_dm_to_alt1 three_d_matching three_d_matching_alt1"
  unfolding is_reduction_def 
  using three_d_matching_to_alt1_sound three_d_matching_to_alt1_complete
  by auto

text "used for example by Wikipedia:
      https://en.wikipedia.org/wiki/3-dimensional_matching#Decision_problem"

definition "three_d_matching_alt2 \<equiv>
    {(T, k). finite T  \<and>
     (\<exists>M \<subseteq> T.  (card M \<ge> k) \<and> self_distinct_components3 M)}"

definition three_dm_to_alt2 where
  "three_dm_to_alt2 = (\<lambda>(U,T). if U \<subseteq> T \<times> T \<times> T \<and> finite T then (U, card T) else ({},1))"

lemma alt2_exact_answer:
  assumes  "(T, k) \<in> three_d_matching_alt2"
  shows  "\<exists>M \<subseteq> T. (card M = k) \<and> self_distinct_components3 M" 
proof -
  obtain M where "M \<subseteq> T"  "card M \<ge> k"  "self_distinct_components3 M"
    using assms  unfolding three_d_matching_alt2_def by auto
  then obtain M' where "M' \<subseteq> M"  "card M' = k" "self_distinct_components3 M'"
    using obtain_subset_with_card_n[of k M] self_distinct_components3_subset
    by metis
  then show ?thesis using \<open>M \<subseteq> T\<close> by blast
qed
 
theorem is_reduction_3dm_to_alt2:
  "is_reduction three_dm_to_alt2 three_d_matching three_d_matching_alt2"
  using infinite_super alt2_exact_answer 
  unfolding is_reduction_def three_d_matching_alt2_def three_dm_to_alt2_def 
            three_d_matching_def
  by (auto, blast)
 

end 