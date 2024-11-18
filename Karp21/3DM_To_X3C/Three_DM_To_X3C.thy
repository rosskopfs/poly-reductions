theory Three_DM_To_X3C
  imports "../XC_To_3DM/Three_DM_Definition" X3C_Definition
begin

datatype 'a X3 = a 'a | b 'a |  c 'a
definition "three_dm_to_x3c \<equiv> (\<lambda>(U,T). ((a `T) \<union> (b `T) \<union> (c `T) , 
                              { {a x, b y, c z} |x  y z.  (x,y,z) \<in> U}))"

lemma three_dm_to_x3c_sound:
  assumes "(U, T) \<in> three_d_matching"
  shows "(three_dm_to_x3c (U,T)) \<in> three_exact_cover"
proof -
  obtain M where M_def:
  "M \<subseteq> U"  "card M = card T"  "self_distinct_components3 M" "finite T" "U \<subseteq> T \<times> T \<times> T"
  "M \<subseteq> T \<times> T \<times> T"
  using assms  unfolding three_d_matching_def by auto
  define S' where "S' = { {a x, b y, c z} |x  y z.  (x,y,z) \<in> M}"
  have "\<Union>S' = (a ` (fst ` M)) \<union> (b ` ((fst \<circ> snd) ` M))  \<union> (c ` ((snd \<circ> snd) ` M))" 
    by (auto simp add: rev_image_eqI S'_def)+ 
  then have "\<Union>S' = (a `T) \<union> (b `T) \<union> (c `T)" 
    using M_def fstM_T sndM_T thrdM_T
    by metis
  then have "(a ` T \<union> b ` T \<union> c ` T, {{a x, b y, c z} |x y z. (x, y, z) \<in> U}) \<in> three_exact_cover"
    using  M_def  S'_def 
    unfolding distinct_components3_def 
    by (intro three_exact_cover_cert[of S']) 
       (fastforce, auto simp add: disjoint_def)
  then show ?thesis unfolding three_dm_to_x3c_def 
    by fast
qed
    

lemma three_dm_to_x3c_complete:
  assumes "(three_dm_to_x3c (U,T)) \<in> three_exact_cover"
  shows "(U, T) \<in> three_d_matching"
proof -
  let ?X = "(a `T) \<union> (b `T) \<union> (c `T)"
  define S where "S = { {a x, b y, c z} |x  y z.  (x,y,z) \<in> U}"
  from assms obtain S' where
    "finite ?X" "\<Union>S \<subseteq> ?X" "S' \<subseteq> S" "\<Union>S' = ?X" "pairwise disjnt S'" "(\<forall>C \<in> S. card C = 3)"
    unfolding three_exact_cover_def three_dm_to_x3c_def S_def
    by auto
  define M' where "M' = {(x,y,z) |x y z. {a x, b y, c z} \<in> S'}"
  show ?thesis 
  proof (intro three_d_matching_cert[of M'])
    have "M' \<subseteq> {(x,y,z) |x y z. {a x, b y, c z} \<in> S}"
      using \<open>S' \<subseteq> S\<close> M'_def 
      by auto
    moreover have "{(x,y,z) |x y z. {a x, b y, c z} \<in> S} = U"
      using insert_absorb S_def by fast
    ultimately show "M' \<subseteq> U" 
      by argo

    show "finite T"
      using \<open>finite ?X\<close>
      by (auto simp add: finite_image_iff inj_on_def)
 
    have "sum card S' = card ?X" 
      using \<open>S' \<subseteq> S\<close> \<open>disjoint S'\<close> \<open>\<Union>S' = ?X\<close>
            card_Union_disjoint  S_def
      by fastforce
    moreover have "... = card T + card T + card T" 
      by (intro card_Un_disjnt[THEN trans] 
          card_image[THEN arg_cong2[where ?f = "(+)",rotated]]
          card_image)
         (auto simp add: inj_on_def disjnt_def \<open>finite T\<close>)
    moreover have \<open>(\<forall>C \<in> S'. card C = 3)\<close> 
        using \<open>(\<forall>C \<in> S. card C = 3)\<close> \<open>S' \<subseteq> S\<close> 
        by blast
    ultimately have "card T = card S'"
        by fastforce  
    also{
      have *:  "M' = (\<lambda>(x, y, z). {a x, b y, c z}) -` S'"
        using M'_def by fastforce
      have "card S' = card M'" 
        using  \<open>S' \<subseteq> S\<close> S_def subsetD inj_def
        by (subst *, intro card_vimage_inj[symmetric]) 
           (auto simp add:inj_def, fastforce) 
    }
    finally show "card M' = card T" 
      by argo

    show "U \<subseteq> T \<times> T \<times> T"
      using \<open>\<Union>S \<subseteq> ?X\<close> S_def 
      by (auto, blast+)   

    show "self_distinct_components3 M'"
      using \<open>pairwise disjnt S'\<close>
      unfolding M'_def distinct_components3_def \<open>pairwise disjnt S'\<close> disjoint_def
      by (auto) fast+
  qed
qed

theorem is_reduction_three_dm_to_x3c:
  "is_reduction three_dm_to_x3c three_d_matching three_exact_cover"
  unfolding is_reduction_def 
  using three_dm_to_x3c_sound three_dm_to_x3c_complete
  by auto
  
           
end