theory VC_To_SC_poly
  imports "../Polynomial_Reductions" 
          VC_To_SC "../IS_To_VC/IS_To_VC_poly"
begin

section \<open>\<open>Vertex Cover\<close> To \<open>Set Cover\<close>\<close>

definition "mop_set_to_list V = SPEC (\<lambda>xs. set xs = V \<and> distinct xs) (\<lambda>_. 1)"

definition "mop_set_member S s = SPECT [ s \<in> S \<mapsto> 1] "

definition "mop_check_ugraph E = SPECT [ugraph E \<mapsto> 1]"


definition "innerset = (\<lambda>v es.
 do {
  Rv \<leftarrow> mop_set_empty_set;
  Rv \<leftarrow> nfoldli es (\<lambda>_. True)
          (\<lambda>e Rv. do { 
                    b \<leftarrow> mop_set_member e v;
                    if b then mop_set_insert Rv e
                       else RETURNT Rv})
      Rv;
  RETURNT Rv
})"

definition "innerset_spec v es = SPECT [  {e. e \<in> (set es) \<and> v \<in> e} \<mapsto> (1+1) * length es + 1 ]"

lemma innerset_refines:
  "innerset v es \<le> innerset_spec v es"
proof -
  let ?I="\<lambda>xs ys S. S = {e. e \<in> set xs \<and> v \<in> e} "

  show ?thesis
    unfolding innerset_def innerset_spec_def  mop_set_empty_set_def mop_set_member_def mop_set_insert_def
    apply(subst nfoldliIE_def[symmetric, where I="?I" and E="2"])
    apply(rule T_specifies_I)
    apply(vcg' \<open>-\<close> rules: T_SPEC )
    unfolding mop_set_empty_set_def
    apply(vcg' -) 
    apply(rule nfoldliIE_rule[THEN T_specifies_rev, THEN T_conseq4, where P2="?I es []" ])
    subgoal apply simp done
    subgoal unfolding mop_set_insert_def
      apply(rule T_specifies_I)
      apply(vcg' \<open>-\<close> rules:  ) unfolding Some_le_emb'_conv Some_eq_emb'_conv
      by (auto simp add: one_enat_def split: if_splits)    
    subgoal by auto 
    subgoal by auto 
     apply (rule order.refl) 
    subgoal apply(vcg' -) unfolding Some_le_emb'_conv Some_eq_emb'_conv
      by (auto simp add: one_enat_def split: if_splits) 
    done
qed

definition "outerset = (\<lambda>es vs.
  do {
    R \<leftarrow> mop_set_empty_set;
    R \<leftarrow> nfoldli vs (\<lambda>_. True)
       (\<lambda>v R. do {
              Rv \<leftarrow> innerset v es;
              R \<leftarrow> mop_set_insert R Rv;
               RETURNT R })
         R;
    RETURNT R
  })" 

definition "outerset_spec es vs
       = SPECT [  {{e. e \<in> set es \<and> v \<in> e} | v. v \<in> set vs} \<mapsto> 1 + ( 2 + (1+1) * length es) * length vs]"

lemmas aha = innerset_refines[unfolded innerset_spec_def,
                THEN T_specifies_rev, THEN T_conseq4]

lemma outerset_refines:
  "outerset es vs \<le> outerset_spec es vs"
proof -
  let ?I="\<lambda>xs ys S. S = {{e. e \<in> set es \<and> v \<in> e} | v. v \<in> set xs} "

  show ?thesis
    unfolding outerset_def outerset_spec_def  mop_set_empty_set_def
    apply(subst nfoldliIE_def[symmetric, where I="?I" and E="2*length es + 2"])
    apply(rule T_specifies_I)
    apply(vcg' \<open>-\<close> rules: T_SPEC )
    unfolding mop_set_empty_set_def
    apply(vcg' -) 
    apply(rule nfoldliIE_rule[THEN T_specifies_rev, THEN T_conseq4, where P2="?I vs []" ])
    subgoal apply simp done
    subgoal unfolding mop_set_insert_def
      apply(rule T_specifies_I)
      apply(vcg' \<open>-\<close> rules: aha) unfolding Some_le_emb'_conv Some_eq_emb'_conv
      by (auto simp add: one_enat_def split: if_splits)    
    subgoal by auto 
    subgoal by auto 
     apply (rule order.refl) 
    subgoal apply(vcg' -) unfolding Some_le_emb'_conv Some_eq_emb'_conv
      by (auto simp add: one_enat_def split: if_splits) 
    done
qed


definition "vc_to_sc = (\<lambda>(E,k).   
  do {
    b \<leftarrow> mop_check_ugraph E;
    V  \<leftarrow> mop_get_vertices E;
    cV \<leftarrow> mop_set_card V;
    vs \<leftarrow> mop_set_to_list V;
    if b \<and> k \<le> cV then
      do {
        es \<leftarrow> mop_set_to_list E;
        ASSERT (length vs \<le> 2 * length es);
        ASSERT (length es = card E);
        R \<leftarrow> outerset es vs;
        RETURNT ( R, k)
      }
    else RETURNT ( {{undefined}}, 0 )
  } )"



definition "sc_time n = 1+1+ (2 * n + 1) + 1 + 1 + (1 + ( 1 + (1+1) * n) * (4*n))" 


lemmas aha2 = outerset_refines[unfolded outerset_spec_def,
                THEN T_specifies_rev, THEN T_conseq4]

lemma pf: "a\<le>b \<Longrightarrow> enat a \<le> enat b" by auto 
lemma k: "enat a + enat b = enat (a+b)" by auto
 

lemma card_Un: "finite E \<Longrightarrow> card (\<Union>E) \<le> sum card E"
  by(induct  rule: finite_induct) (auto intro: order.trans[OF card_Un_le]) 

lemma vc_to_sc_refines:
  "vc_to_sc (E,k) \<le> SPEC (\<lambda>y. y = vc_sc (E,k)) (\<lambda>_. sc_time (size_VC (E,k)))"
  unfolding SPEC_def
  unfolding vc_to_sc_def vc_sc_def   
      mop_set_to_list_def mop_get_vertices_def mop_set_card_def
      mop_check_ugraph_def
  apply(rule T_specifies_I)
  apply(vcg' \<open>-\<close> rules: T_SPEC aha2)
  subgoal apply simp  apply safe
       apply(auto split: if_splits) 
    subgoal premises prems apply(auto simp: sc_time_def size_VC_def)
      unfolding one_enat_def apply simp
      apply(rule add_mono)   
      subgoal using prems(8,9) by auto
      subgoal using prems(8,9) apply(intro mult_mono) by auto
      done
    done 
  subgoal
    by(auto simp: distinct_card)
  subgoal    for a b x xa
    unfolding ugraph_def apply auto
    subgoal premises prems
    proof -
      have "length x = card (\<Union> a)" 
        apply(subst distinct_card[symmetric])
        using prems  by auto
      also have "\<dots> \<le> sum card a"
        apply(rule card_Un) using prems by simp
      also have "\<dots> = sum card (set xa)" using prems by auto
      also have "\<dots> = 2 * card (set xa)" using prems by simp
      also have "\<dots> = 2 * length xa" 
        apply(subst distinct_card[symmetric])using prems by auto
      finally show ?thesis .
    qed
    done
  subgoal
    apply auto
    unfolding Some_le_emb'_conv Some_eq_emb'_conv
    by (auto simp: size_IS_def size_VC_def sc_time_def  one_enat_def) 
  done



definition "size_SC = (\<lambda>(E,k). sum card E)"

definition "sc_space n = 1 + 2 * (n * n)" 
  

lemma sum_Un: "finite E \<Longrightarrow> (\<And>e. e\<in>E \<Longrightarrow> finite e) \<Longrightarrow> (\<And>x. f x \<ge> (0::nat))
     \<Longrightarrow> sum f (\<Union>E) \<le> sum (\<lambda>x. sum f x) E"
  by (induct  rule: finite_induct) 
    (simp_all add: sum_Un_nat) 


lemma vc_to_sc_size:
  "size_SC (vc_sc a) \<le> sc_space (size_VC a)"
  apply(cases a)
  apply (auto simp: vc_sc_def size_SC_def size_VC_def vc_time_def sc_space_def)
  subgoal premises prems for E k
  proof -
    have *: "{{e \<in> E. v \<in> e} |v. \<exists>x\<in>E. v \<in> x} = (\<lambda>v. {e \<in> E. v \<in> e}) ` (\<Union> E)" by blast
    have "sum card {{e \<in> E. v \<in> e} |v. \<exists>x\<in>E. v \<in> x}
      = sum card ((\<lambda>v. {e \<in> E. v \<in> e}) ` (\<Union> E))" unfolding * ..
    also have "\<dots> \<le> sum (card o (\<lambda>v. {e \<in> E. v \<in> e})) (\<Union> E)"
      apply(rule sum_image_le) using prems(2) ugraph_vertex_set_finite by auto
    also have "\<dots> \<le> sum (\<lambda>x. sum (card o (\<lambda>v. {e \<in> E. v \<in> e})) x) E " apply(rule sum_Un)
      using prems unfolding ugraph_def apply auto  
      by (meson finite_subset le_cSup_finite prems(2) ugraph_vertex_set_finite)  
    also have "\<dots> \<le> sum (\<lambda>x. sum (\<lambda>_. card E) x) E"
      apply(rule sum_mono)
      apply(rule sum_mono) apply auto  
      by (metis (no_types, lifting) card_mono mem_Collect_eq prems(2) subsetI ugraph_def)   
    also have "\<dots> = sum (\<lambda>x. 2 * card E) E" 
      apply(rule sum.cong) using prems(2) unfolding ugraph_def by simp_all
    also have "\<dots> = 2* (card E) * (card E)" by simp
    finally show ?thesis by simp
  qed
  done


theorem vc_to_sc_ispolyred: "ispolyred vc_to_sc vertex_cover set_cover size_VC size_SC" 
  unfolding ispolyred_def
  apply(rule exI[where x=vc_sc])
  apply(rule exI[where x=sc_time])
  apply(rule exI[where x=sc_space])
  apply(safe)
  subgoal using vc_to_sc_refines by blast
  subgoal using vc_to_sc_size  by blast 
  subgoal unfolding poly_def sc_time_def apply(rule exI[where x=2]) by auto
  subgoal unfolding poly_def sc_space_def apply(rule exI[where x=2]) by auto
  subgoal using is_reduction_vc_sc .
  done

end