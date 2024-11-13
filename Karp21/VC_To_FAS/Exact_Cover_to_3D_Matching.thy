theory Exact_Cover_to_3D_Matching
  imports Main "HOL-Library.Disjoint_Sets" "List-Index.List_Index"
          "../SAT_To_XC/XC_Definition"
        
begin


(* helper lemmas *)
lemma mod_SucE: " Suc a mod k = Suc b mod k
                  \<Longrightarrow> a mod k = b mod k"
  using mod_Suc 
  by (metis nat.inject nat.simps(3))

lemma finite_Collect_mem:
  assumes  "inj_on f P" 
  shows    "finite {f x|x. x \<in> P} =  finite P"
  by (simp add: Setcompr_eq_image assms finite_image_iff)

(* also in VC_to_Fas: move somewhere *)
lemma card_Collect_mem:
  assumes  "inj_on f P"
  shows    "card {f x|x. x \<in> P} = card P"
  by (simp add: assms card_image setcompr_eq_image)



lemma card_discriminated_union:
  assumes fin_s: "\<And>s. s \<in> S \<Longrightarrow> finite s" 
  shows "card {(x, s) | s x. s \<in> S \<and> x \<in> s} = sum card S"
proof -    
  have dis: "disjoint {{(x,s) | x. x \<in> s} |s. s \<in> S}"
    unfolding disjoint_def by auto
  have  "card {(x,s) |s x. s \<in> S \<and> x \<in> s} =
         card ( \<Union>  {{(x,s) | x. x \<in> s} |s. s \<in> S})"
    by (intro arg_cong[where ?f = "card"]) auto
  also have "... = sum card ((\<lambda>s. {(x,s) | x. x \<in> s})  ` S)"
    using fin_s card_Union_disjoint[OF dis]
    by (auto simp add: Setcompr_eq_image)
  also have "... = sum card S"
  proof - 
    have inj: "inj_on (\<lambda>s. {(v,s) | v. v \<in> s}) S" 
      unfolding inj_on_def by blast
    show ?thesis       
      by (subst sum.reindex[OF inj], intro sum.cong)
         (auto simp add: Setcompr_eq_image card_image inj_on_def)
  qed
  finally show ?thesis .
qed

lemma finite_discriminated_union:
  assumes "finite (\<Union>S)"
  shows "finite {(x, s) | s x. s \<in> S \<and> x \<in> s}"
proof -
  have fin_s: "\<And>s. s \<in> S \<Longrightarrow> finite s"
    using assms  by (meson Union_upper finite_subset)
  then have "card {(x, s) | s x. s \<in> S \<and> x \<in> s}  \<ge> card (\<Union>S)"
    by (simp add: card_Union_le_sum_card card_discriminated_union)
  then show ?thesis 
    using assms not_finite_existsD order_antisym_conv by fastforce
qed

(* needed for completness, 
   prove that there is an inj from US to discrimnated union S *)
lemma finite_discriminated_union_finite_union:
  assumes "finite {(x, s) | s x. s \<in> S \<and> x \<in> s}"
  shows "finite (\<Union>S)"
  sorry 






section \<open>Definitions\<close>


subsection \<open>3D Matching Problem\<close>

definition componentwise_different3 where
 "componentwise_different3 M1 M2 = (\<forall>(a, b, c) \<in> M1. 
                    \<forall>(a1, b1, c1) \<in> M2. 
                     (a = a1 \<or> b = b1 \<or> c = c1) \<longrightarrow> (a, b, c) = (a1, b1, c1))"

abbreviation self_componentwise_different3 where
 "self_componentwise_different3  M \<equiv> componentwise_different3 M M "

lemma self_componentwise_different3_injI:
  assumes "inj_on f S"
          "inj_on g S"
          "inj_on h S"
  shows "self_componentwise_different3 {(f x, g x, h x)|x. x \<in> S}"
  using assms unfolding inj_on_def componentwise_different3_def
  by blast

lemma self_componentwise_different3_unionI:
  assumes "self_componentwise_different3 M1"
          "self_componentwise_different3 M2"
          "componentwise_different3 M1 M2"       
  shows "self_componentwise_different3 (M1 \<union> M2)"
  using assms unfolding inj_on_def componentwise_different3_def
  by auto (* auto very slow *)

lemma componentwise_different3I:
  assumes "\<And> a b c a1 b1 c1.
            (a,b,c) \<in> M1 \<Longrightarrow>
            (a1,b1,c1) \<in> M2 \<Longrightarrow>
            (a=a1 \<or> b=b1 \<or> c=c1) \<Longrightarrow> ((a,b,c) = (a1,b1,c1))"
  shows "componentwise_different3  M1 M2"
  using assms unfolding componentwise_different3_def
  by blast
        

definition "three_3d_matching \<equiv> 
    {(U, T). U \<subseteq> (T \<times> T \<times> T) \<and> finite T \<and>
     (\<exists>M \<subseteq> U.  (card M = card T) \<and> self_componentwise_different3 M)}"

lemma three_3d_matching_cert:
  assumes "M \<subseteq> U"
          "card M = card T"
          "U \<subseteq> (T \<times> T \<times> T)"
          "finite T"
          "self_componentwise_different3 M"
  shows "(U,T) \<in> three_3d_matching"
  unfolding three_3d_matching_def using assms
  by blast



section \<open>Reduction from Exact Cover to 3D Matching\<close>

(* turns a set into a list *)

definition to_list where
  "to_list s = (SOME l. set l = s \<and> distinct l)"

lemma to_list_distinct:
  assumes "finite s"
  shows   "set (to_list s) = s \<and> distinct (to_list s)"
  unfolding to_list_def using finite_distinct_list[OF assms]
  by (intro someI_ex[of "\<lambda>l.  set l = s \<and> distinct l"])

(* gets the next element in an arbitrary but fixed order *)

definition nxt where 
"nxt = (\<lambda>(x, s). ((let l = to_list s in
                   l!((Suc (index l x)) mod (length l)) ), s))"

lemma nxt_el:
  assumes "x \<in> s" "finite s"
  shows "\<exists>x'. nxt (x,s) = (x',s) \<and> x' \<in> s"
  unfolding nxt_def Let_def
  using assms to_list_distinct[OF \<open>finite s\<close>] 
        mod_less_divisor[THEN nth_mem, of "to_list s"]
  by (cases "length (to_list s) > 0") force+


definition xc_to_3dm where
  "xc_to_3dm = (\<lambda>(X, S). 
    let 
      T = {(x, s) | s x. s \<in> S \<and> x \<in> s};
      \<alpha> = (SOME f. inj_on f X \<and> f ` X \<subseteq> T );
      U1 = { (\<alpha> x, (x, s), (x, s)) | s x. s \<in> S \<and> x \<in> s };
      U2 = \<Union> { {(\<beta>, (x,s), nxt (x,s)) | s x. s \<in> S \<and> x \<in> s } 
                | \<beta>. \<beta> \<notin> (\<alpha> ` X) \<and> \<beta> \<in> T }
    in 
      (U1 \<union> U2, T)
  )"


  
section \<open>Soundness\<close>

lemma xc_to_3dm_sound:
  assumes "(X, S) \<in> exact_cover"
  shows "xc_to_3dm (X, S) \<in> three_3d_matching"
proof -
  from assms obtain S' where
    "finite X" "\<Union>S \<subseteq> X" "S' \<subseteq> S" "\<Union>S' = X" "pairwise disjnt S'"
    unfolding exact_cover_def by blast

  have "finite (\<Union>S)"  using \<open>\<Union> S \<subseteq> X\<close> \<open>finite X\<close> infinite_super by blast
  then have "finite S"  using finite_UnionD by blast
  have fin_s: "s \<in> S \<Longrightarrow> finite s" for s
    by (meson Sup_upper \<open>finite (\<Union> S)\<close> infinite_super)

  let ?T = "{(x, s) | s x. s \<in> S \<and> x \<in> s}"
  have fin_T: "finite ?T"
     using \<open>finite (\<Union> S)\<close> finite_discriminated_union by blast
 
  define \<alpha> where "\<alpha> = (SOME f.  inj_on f X \<and> f ` X \<subseteq> ?T)"
  have "card X \<le> card ?T" 
  proof -
    have "card ?T = sum card S"
      using card_discriminated_union fin_s by blast
    also have "\<dots> \<ge> sum card S'" using \<open>finite S\<close> \<open>S' \<subseteq> S\<close>
      by (intro sum_mono2) auto
    finally show ?thesis  
      using \<open>\<Union> S' = X\<close> card_Union_le_sum_card le_trans by blast
  qed
  then have inj_\<alpha>: "inj_on \<alpha> X \<and> \<alpha> ` X \<subseteq> ?T" 
    unfolding \<alpha>_def using \<open>finite X\<close> fin_T
    by (intro someI_ex[of "\<lambda>f. inj_on f X \<and> f ` X \<subseteq> ?T"] inj_on_iff_card_le[THEN iffD2])
  

  let ?U1 = "{ (\<alpha> x, (x, s), (x, s)) | s x. s \<in> S \<and> x \<in> s }"
  let ?U2 = " \<Union> { {(\<beta>, (x,s), nxt (x,s))
                | s x. s \<in> S \<and> x \<in> s } 
                | \<beta>. \<beta> \<notin> (\<alpha> ` X) \<and> \<beta> \<in> ?T }"
  let ?U = "?U1 \<union> ?U2"

  

  define A where "A = {(x, s) | s x. s \<in> S' \<and> x \<in> s}"
  have "A \<subseteq> ?T" unfolding A_def using \<open>S' \<subseteq> S\<close> by blast
  then have "finite A" using fin_T rev_finite_subset by blast

  have "card (?T - A) = card (?T - (\<alpha> ` X))"
  proof -
    have "card (?T - A) = card ?T - card A" 
      using \<open>A \<subseteq> ?T\<close> \<open>finite A\<close> card_Diff_subset by blast
    moreover have "card (?T - \<alpha> ` X) = card ?T - card (\<alpha> ` X)"
      using \<alpha>_def \<open>finite X\<close> inj_\<alpha> card_Diff_subset by auto
    moreover{
      have fin_s': "s \<in> S' \<Longrightarrow> finite s" for s
        using \<open>S' \<subseteq> S\<close> fin_s by blast
      then have "card  A = sum card S'"
        using A_def card_discriminated_union by blast
      also have "... = card (\<Union>S')"
        using fin_s' \<open>disjoint S'\<close>
        by (intro card_Union_disjoint[symmetric]) auto
      also have "... = card (\<alpha> ` X)"
        using inj_\<alpha> card_image[symmetric] \<open>\<Union> S' = X\<close> by fast
      finally have "card A = card (\<alpha> ` X)".
    }
    ultimately show ?thesis by argo
  qed
  then obtain \<beta> where \<beta>_bij: "bij_betw \<beta> (?T - A) (?T - (\<alpha> ` X))"
    using finite_same_card_bij finite_Diff fin_T
    by meson

  define f where "f = (\<lambda>(x, (s::'a set)). \<alpha> x)"


  let ?M1 = "{ (f u, u, u) |u. u \<in> A }"
  let ?M2 = "{ (\<beta> u, u, nxt u)|u. u \<in> (?T - A)}"
  let ?M = "?M1 \<union> ?M2"
  
  have "(?U, ?T) \<in> three_3d_matching"
  proof (intro three_3d_matching_cert[of ?M])
    show "finite ?T" using fin_T.
    show  "?U \<subseteq> ?T \<times> ?T \<times> ?T"  using inj_\<alpha> \<open>\<Union>S \<subseteq> X\<close> nxt_el fin_s
      by (auto, blast, meson) 
    show "?M \<subseteq> ?U" 
    proof -
      have "(\<beta> u, u, nxt u) \<in> ?U2"  if "u \<in> (?T - A)" for u 
      proof -
        have *:"\<beta> u  \<notin> (\<alpha> ` X) \<and> \<beta> u \<in> ?T" 
          using \<beta>_bij bij_betwE that by fastforce
        moreover have "(\<beta> u, u, nxt u) \<in>  {(\<beta> u, (x, s), nxt (x, s)) |s x. s \<in> S \<and> x \<in> s}"
          using that by blast
        moreover have "{(\<beta> u, (x, s), nxt (x, s)) |s x. s \<in> S \<and> x \<in> s} \<in>  
                { {(\<beta>, (x,s), nxt (x,s))
                | s x. s \<in> S \<and> x \<in> s } 
                | \<beta>. \<beta> \<notin> (\<alpha> ` X) \<and> \<beta> \<in> ?T }"  
          using "*" that by fastforce
        ultimately show ?thesis  using that 
          by (meson UnionI)
      qed
      then have "?M2 \<subseteq> ?U2"  by blast
      moreover have "?M1 \<subseteq> ?U1" unfolding f_def A_def
        using \<open>S' \<subseteq> S\<close> by auto
      ultimately show ?thesis 
        by (meson sup_mono)
    qed
    
    show "card ?M = card ?T"
    proof -
      have "finite ?M1" using inj_on_def \<open>finite A\<close>
        by (intro card_Un_disjoint finite_Collect_mem[THEN iffD2]) auto
      moreover have "finite ?M2" using inj_on_def fin_T
        by (intro finite_Collect_mem[THEN iffD2]) blast+
      ultimately have "card ?M = card ?M1 + card ?M2" 
        by (intro card_Un_disjoint) auto    
      moreover have "card ?M1 = card A" 
        by (intro card_Collect_mem) (simp add: inj_on_def) 
      moreover have "card ?M2 = card (?T - A)"
        by (intro card_Collect_mem) (simp add: inj_on_def)
      moreover have "card ?T = card A  + card (?T - A)"
        using card_Int_Diff[of ?T A] 
        by (simp add: Int_absorb1 \<open>A \<subseteq> ?T\<close> fin_T)
      ultimately show ?thesis by argo
    qed

    show  "self_componentwise_different3 ?M" using inj_on_id
    proof (intro self_componentwise_different3_unionI 
                 self_componentwise_different3_injI)
      show "componentwise_different3 ?M1 ?M2"
      proof(intro componentwise_different3I) 
        fix a b c a1 b1 c1
        assume in_M1: "(a, b, c) \<in> ?M1"
        assume in_M2: "(a1, b1, c1) \<in> ?M2"
        have "b \<noteq> b1" using in_M1 in_M2 by blast
        moreover {
          have "c1 = nxt b1" using in_M2 by blast
          then have "snd c1 = snd b1" by (simp add: case_prod_unfold nxt_def)  
          then have "snd c1 \<noteq> snd b" 
            using \<open>b \<noteq> b1\<close>  A_def in_M1 in_M2 by force
          then have "c \<noteq> c1" using in_M1 by blast
        }
        moreover {
          have "\<beta> b1 \<notin> (\<alpha> ` X)" 
            using \<beta>_bij bij_betw_apply in_M2 by fastforce
          moreover have "f b \<in> (\<alpha> ` X)" 
            using A_def \<open>\<Union> S' = X\<close> f_def in_M1 by auto
          ultimately have "a \<noteq> a1"  using in_M1 in_M2 by auto
        }
        ultimately show "(a = a1 \<or> b = b1 \<or> c = c1) \<Longrightarrow> (a, b, c) = (a1, b1, c1)"
          by simp
      qed
      show "inj_on f A"
      proof (intro inj_onCI)
        fix x y
        assume "x \<in> A" "y \<in> A" "f x = f y" "x \<noteq> y"
        obtain a s b s' where *:"x = (a,s)" "a \<in> s" "s \<in> S'" 
                                "y = (b,s')" "b \<in> s'" "s' \<in> S'"
          using A_def \<open>x \<in> A\<close> \<open>y \<in> A\<close>  by blast
        have "a \<noteq> b" using disjoint_def \<open>disjoint S'\<close> * \<open>x \<noteq> y\<close>
          by (cases "s = s'") fast+
        moreover have "\<alpha> a = \<alpha> b" using \<open>f x = f y\<close> 
          by (simp add: "*" f_def)
        ultimately show False 
          by (meson "*" UnionI \<open>S' \<subseteq> S\<close> \<open>\<Union> S \<subseteq> X\<close> in_mono inj_\<alpha> inj_on_def)
      qed
      show "inj_on \<beta> (?T - A)" using \<beta>_bij bij_betw_def by blast
      show "inj_on nxt (?T-A)"
      proof (intro inj_on_diff inj_onI)  
        fix x y
        assume "x \<in>?T" "y \<in> ?T" "nxt x = nxt y"
        then obtain x' y' s where x'y'_def:"x = (x',s)" "y = (y',s)"
          unfolding nxt_def by fastforce
        then have "finite s"  using Union_upper \<open>finite (\<Union> S)\<close> \<open>y \<in> ?T\<close> infinite_super
          by fastforce
        let ?l = "to_list s"
        have "?l ! ((Suc (index ?l x')) mod length ?l) =
            ?l ! ((Suc (index ?l y')) mod length ?l) "
          using \<open>nxt x = nxt y\<close> x'y'_def unfolding nxt_def Let_def by fast
        then have "(Suc (index ?l x')) mod length ?l = (Suc (index ?l y')) mod length ?l"
          using to_list_distinct[OF \<open>finite s\<close>]
          by (cases ?l) (simp add: nth_eq_iff_index_eq)+
        then have "index ?l x'  mod length ?l = index ?l y'  mod length ?l" 
          by (rule mod_SucE)
        then have "x' = y'"  using \<open>finite s\<close> \<open>x \<in> ?T\<close> \<open>y \<in> ?T\<close> to_list_distinct x'y'_def
          by fastforce
        then show "x = y"  by (simp add: x'y'_def)
      qed

(* how do I get rid of these *) 
      thm inj_on_id
      show "inj_on (\<lambda>x. x) A" by simp
      show "inj_on (\<lambda>x. x) A" by simp
      show "inj_on (\<lambda>x. x) ({(x, s) |s x. s \<in> S \<and> x \<in> s} - A)" by simp
    qed
  qed
  then show ?thesis  unfolding xc_to_3dm_def Let_def
    using \<alpha>_def by force
qed


section \<open>Completness\<close>
lemma xc_to_3dm_complete:
  assumes "xc_to_3dm (X, S) \<in> three_3d_matching"
  shows "(X, S) \<in> exact_cover"
proof -
  let ?T = "{(x, s) | s x. s \<in> S \<and> x \<in> s}"
  define \<alpha> where "\<alpha> = (SOME f.  inj_on f X \<and> f ` X \<subseteq> ?T)"
  let ?U1 = "{ (\<alpha> x, (x, s), (x, s)) | s x. s \<in> S \<and> x \<in> s }"
  let ?U2 = " \<Union> { {(\<beta>, (x,s), nxt (x,s))
                | s x. s \<in> S \<and> x \<in> s } 
                | \<beta>. \<beta> \<notin> (\<alpha> ` X) \<and> \<beta> \<in> ?T }"
  let ?U = "?U1 \<union> ?U2"
 
  obtain M where "M\<subseteq>?U" "card M = card ?T"  "self_componentwise_different3 M"
                 "finite ?T" "?U \<subseteq> ?T \<times> ?T \<times> ?T"
    using assms unfolding three_3d_matching_def xc_to_3dm_def Let_def \<alpha>_def
    by auto

  define S' where "S' = {s |s x. (\<alpha> x, (x, s), (x, s)) \<in> (?U1 \<inter> M)}"
                                 
  
  have "(X, S) \<in> exact_cover"
  proof (intro exact_cover_I[of S'])
    show "S' \<subseteq> S"  unfolding S'_def by blast
    have "\<Union>S = X" sorry (* force it later by changing the reduction*)
    show "\<Union>S \<subseteq> X"  by (simp add: \<open>\<Union> S = X\<close>)
    show "finite X" using finite_discriminated_union_finite_union
                          \<open>finite ?T\<close> \<open>\<Union> S = X\<close> by blast
    have "X \<subseteq>  \<Union>S'"
    proof 
      fix x assume "x \<in> X"
      then obtain s where "x \<in> s" and "s \<in> S" 
        using \<open>\<Union>S = X\<close> by fast
      then have "\<alpha> x \<in> ?T" using \<open>?U \<subseteq> ?T \<times> ?T \<times> ?T\<close>
        by blast
      moreover {
        have "fst ` M \<subseteq> ?T" using \<open>M \<subseteq> ?U\<close> \<open>?U \<subseteq> ?T \<times> ?T \<times> ?T\<close>
          by fastforce 
        moreover have "card (fst ` M) = card ?T" 
          using \<open>self_componentwise_different3 M\<close> \<open>card M = card ?T\<close>
          by (intro card_image[THEN trans]) 
            (auto simp add: inj_on_def componentwise_different3_def fst_def)
        ultimately have "fst ` M = ?T" 
          by (simp add: \<open>finite ?T\<close> card_subset_eq)
      }
      ultimately have "\<alpha> x \<in> fst ` M" by blast
      moreover have "\<alpha> x \<notin> fst ` ?U2" 
        sorry
      ultimately have "\<alpha> x \<in> fst ` ?U1"
        sorry
      oops

      
        
        
      
        


     

   
end