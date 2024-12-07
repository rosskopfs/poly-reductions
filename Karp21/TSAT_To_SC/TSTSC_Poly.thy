subsection\<open>The reduction from \<open>3CNF-SAT\<close> To \<open>Set Cover\<close> is polynomial\<close>

theory TSTSC_Poly
  imports "../Polynomial_Reductions" TSAT_To_SC
begin

definition "size_IS = (\<lambda>(E,k). card E)"
definition "size_VC = (\<lambda>(E,k). card E)"

subsubsection \<open>\<open>Independent Set\<close> To \<open>Vertex Cover\<close>\<close>

paragraph \<open>A trivial implementation\<close>

text \<open>Here we assume that we have an operation that returns
      the size of the set of vertices.\<close>

definition "mop_get_vertices E = REST [ (\<Union> E)  \<mapsto> 2 * card E + 1]"

definition "mop_get_vertices_card E = REST [(card (\<Union> E)) \<mapsto> 2 * card E + 2]"

text \<open>Then we can easily give an abstract algorithm for the reduction:\<close>

definition "is_to_vc = (\<lambda>(E,k). 
          do {
            s \<leftarrow> mop_get_vertices_card E;
            if k > s  then
              RETURNT (E,k)
            else
              RETURNT (E, s-k)
          })"

definition "vc_time n = 2 * n + 2" 
definition "vc_space n = n" 


lemma is_to_vc_refines:
  "is_to_vc vc \<le> SPEC (\<lambda>y. y = is_vc vc) (\<lambda>_. vc_time (size_IS vc))"
  unfolding is_to_vc_def is_vc_def SPEC_def mop_get_vertices_card_def
  apply(rule T_specifies_I)
  apply(vcg' \<open>-\<close>)
  by (auto simp: size_IS_def size_VC_def vc_time_def vc_space_def) 

lemma is_to_vc_size:
  "size_VC (is_vc a) \<le> vc_space (size_IS a)"
  apply(cases a)
  by (auto simp: is_vc_def size_IS_def size_VC_def vc_time_def vc_space_def) 

thm is_reduction_is_vc


text \<open>And we show that it actually is a polynomial reduction:\<close>

theorem is_to_vc_ispolyred: "ispolyred is_to_vc independent_set vertex_cover size_IS size_VC" 
  unfolding ispolyred_def
  apply(rule exI[where x=is_vc])
  apply(rule exI[where x=vc_time])
  apply(rule exI[where x=vc_space])
  apply(safe)
  subgoal using is_to_vc_refines by blast
  subgoal using is_to_vc_size  by blast 
  subgoal unfolding poly_def vc_time_def apply(rule exI[where x=1]) by auto
  subgoal unfolding poly_def vc_space_def apply(rule exI[where x=1]) by simp
  subgoal using is_reduction_is_vc .
  done



paragraph \<open>A more fine grained algorith\<close>

text \<open>now we assume to only have more fine grained basic operations.\<close>

text \<open>This setup is actually unrealistic, it is hard to imagine a datastructure with
  constant insertion and constant cardinality query.
     TODO: make cost of insert linear in size of S\<close>

definition "mop_set_insert S s = REST [insert s S \<mapsto> 1]"

definition "mop_set_card S  = REST [card S \<mapsto> 1]"

definition "mop_set_empty_set = REST [ {} \<mapsto> 1]"


text \<open>Now we want to work on lists of tuples to represent the Edge set:\<close>

definition "R_edge_set_tuple_list = {(xs,E) |xs E. ((\<lambda>(a,b). {a,b}) ` (set xs) = E \<and> distinct xs
           \<and> inj_on (\<lambda>(a,b). {a,b}) (set xs)  )}"
text \<open>here the constraint @{term inj_on} means, that the edge list xs
       does not contain any loops ( (a,a) ),
        or both symmetric edges ( (a,b)\<in>set xs \<and> (b,a)\<in>set xs )\<close> 


text \<open>we can restate the specification to get the cardinality of the set of vertices given
      an edge list, and that it refines the operation @{term mop_get_vertices_card}\<close>

definition "mop_get_vertices_card' xs = REST [(card (\<Union> ((\<lambda>(a,b). {a,b}) ` (set xs)))) \<mapsto> 2 * length xs + 2]"

lemma mop_get_vertices_card_data_refine:  
  assumes "(xs,E)\<in>R_edge_set_tuple_list"
  shows "mop_get_vertices_card' xs \<le> mop_get_vertices_card E"
proof -
  from assms have E: "E = (\<lambda>(a,b). {a,b}) ` (set xs)"
     and *: "distinct xs""inj_on (\<lambda>(a,b). {a,b}) (set xs)"
    unfolding R_edge_set_tuple_list_def by auto
  have **: "card E = length xs" 
    by(simp add: card_image distinct_card E *)
  show ?thesis    
    unfolding mop_get_vertices_card'_def mop_get_vertices_card_def
    unfolding ** by(simp add: E)
qed

text \<open>now let's implement getting the cardinality of V with the basic set operations\<close>

definition "mop_get_vertices' es = SPECT [\<Union> ((\<lambda>(a,b). {a,b}) ` (set es)) \<mapsto> 2 * length es + 1]"

definition get_vertices where
  "get_vertices es = 
    do { S \<leftarrow> mop_set_empty_set;
      S' \<leftarrow> nfoldli es (\<lambda>_. True) 
            (\<lambda>(a,b) S. do {
                  S \<leftarrow> mop_set_insert S a;
                  S \<leftarrow> mop_set_insert S b;
                  RETURNT S }) 

        S;
      RETURNT S' 
  }"


lemma get_vertices_refine:
  "get_vertices xs \<le> mop_get_vertices' xs"
proof -
  let ?I = "\<lambda>(xs::('b*'b)list) ys (S::'b set).  S = \<Union> ((\<lambda>(a,b). {a,b}) ` (set xs))"

  show ?thesis
  unfolding get_vertices_def mop_get_vertices'_def
  apply(rule T_specifies_I)
  apply(subst nfoldliIE_def[symmetric, where I="?I" and E=2])
  unfolding mop_set_empty_set_def
  apply(vcg' -) 
  apply(rule nfoldliIE_rule[THEN T_specifies_rev, THEN T_conseq4, where P2="?I xs []" ])
       apply simp
  subgoal 
    apply(rule T_specifies_I)
    unfolding mop_set_insert_def
    apply(vcg' -)
    apply auto unfolding Some_le_emb'_conv
    by auto
     apply simp
    apply simp
  apply (rule order.refl)
  unfolding mop_set_card_def
  apply (vcg' -) apply auto unfolding Some_le_emb'_conv Some_eq_emb'_conv
   apply (auto simp add: one_enat_def)    
  done 
qed

definition get_vertices_card :: "('b*'b) list \<Rightarrow> nat nrest" where
  "get_vertices_card es = do {
      V \<leftarrow> get_vertices es;
      n \<leftarrow> mop_set_card V;
      RETURNT n
    }"
 
thm get_vertices_refine[unfolded mop_get_vertices'_def,
                THEN T_specifies_rev, THEN T_conseq4]

lemma get_vertices_card_refine:
  "get_vertices_card xs \<le> mop_get_vertices_card' xs" 
  unfolding get_vertices_card_def mop_get_vertices_card'_def
  apply(rule T_specifies_I) 
  apply(vcg' - rules: get_vertices_refine[unfolded mop_get_vertices'_def,
                THEN T_specifies_rev, THEN T_conseq4]) 
  unfolding mop_set_card_def
  apply (vcg' -) unfolding Some_le_emb'_conv Some_eq_emb'_conv
  by (auto simp add: one_enat_def split: if_splits)    
 

lemma get_vertices_card_data_refine:
  assumes "(xs,E)\<in>R_edge_set_tuple_list"
  shows "get_vertices_card xs \<le>  (mop_get_vertices_card E)"
  apply(rule order.trans) 
  apply(rule   get_vertices_card_refine)
  apply(rule mop_get_vertices_card_data_refine)
  by fact

text \<open>now we can give a refined algorithm, only using the fine grained operations:\<close>

definition "is_to_vc2 = (\<lambda>(xs,k). 
          do {
            s \<leftarrow> get_vertices_card xs;
            if k > s  then
              RETURNT (xs,k)
            else
              RETURNT (xs, s-k)
          })"


lemma R_reintro: "A \<le>   B \<Longrightarrow> A \<le> \<Down>Id B" by simp

term " prod_rel R_edge_set_tuple_list Id"
lemma is_to_vc2_refines:
  "((xs,k),(E,k)) \<in> R_edge_set_tuple_list \<times>\<^sub>r Id
     \<Longrightarrow> is_to_vc2 (xs,k) \<le> \<Down> (R_edge_set_tuple_list \<times>\<^sub>r Id) (is_to_vc (E,k))"
  unfolding is_to_vc_def is_to_vc2_def
  apply (refine_rcg get_vertices_card_data_refine[THEN R_reintro] )
  subgoal by (auto simp: prod_rel_def_internal)
  subgoal by (auto simp: prod_rel_def_internal)
  subgoal by (auto simp: RETURNT_refine prod_rel_def_internal)
  subgoal by(auto intro!: RETURNT_refine simp: prod_rel_def_internal)
  done
lemma is_to_vc2_refines':
  "(i',i) \<in> R_edge_set_tuple_list \<times>\<^sub>r Id
     \<Longrightarrow> is_to_vc2 i' \<le> \<Down> (R_edge_set_tuple_list \<times>\<^sub>r Id) (is_to_vc i)"
  unfolding is_to_vc_def is_to_vc2_def
  apply (refine_rcg get_vertices_card_data_refine[THEN R_reintro] )
  subgoal by (auto simp: prod_rel_def_internal)
  subgoal by (auto simp: prod_rel_def_internal)
  subgoal by (auto simp: RETURNT_refine prod_rel_def_internal)
  subgoal by(auto intro!: RETURNT_refine simp: prod_rel_def_internal)
  done


thm ispolyredd_refine[OF is_to_vc_ispolyred[THEN ispolyredd_generalizes_ispolyredD] is_to_vc2_refines' ]
    is_to_vc2_refines

text \<open>Finally we can show that the new algorithm also is a polynomial reduction acting on 
      lists of tuples instead of an abstract edge set\<close>

theorem "ispolyredd is_to_vc2
       (R_edge_set_tuple_list \<times>\<^sub>r nat_rel) (R_edge_set_tuple_list \<times>\<^sub>r nat_rel)
        independent_set vertex_cover size_IS size_VC"
  apply(rule ispolyredd_refine[OF is_to_vc_ispolyred[THEN ispolyredd_generalizes_ispolyredD], simplified])
  apply(rule is_to_vc2_refines' ) .


subsubsection \<open>\<open>Vertex Cover\<close> To \<open>Set Cover\<close>\<close>

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


subsubsection \<open>\<open>3CNF-SAT\<close> To \<open>Independent Set\<close>\<close>

definition "mop_list_length xs = SPECT [ length xs \<mapsto> 1 ]"

definition "add_first_part F S = 
  SPECT [ S \<union> {{(l1, i), (l2, i)} | l1 l2 i. i < length F \<and> l1 \<in> F ! i \<and> l2 \<in> F ! i \<and> l1 \<noteq> l2} \<mapsto> 3 * length F]"

      
definition "add_second_part F S = 
  SPECT [ S \<union> {{(l1, i), (l2, j)} | l1 l2 i j.
      i < length F \<and> j < length F \<and> l1 \<in> F ! i \<and> l2 \<in> F ! j \<and> conflict l1 l2}
       \<mapsto> 3 * length F * length F]"



definition sat_to_is :: "'a lit set list \<Rightarrow> (('a lit \<times> nat) set set \<times> nat) nrest" where 
  "sat_to_is = (\<lambda>F. do {
      b \<leftarrow> SPECT [ (\<forall>cls \<in> set F. card cls = 3) \<mapsto> 1];
      if b then
        do {
          l \<leftarrow> mop_list_length F; 
          S \<leftarrow> mop_set_empty_set;
          S \<leftarrow> add_first_part F S;
          S \<leftarrow> add_second_part F S;
          RETURNT ( S, l)
        }
      else RETURNT ( {}, 1 )
    })"

definition "size_SAT xs = length xs"
definition "sat_to_is_time n = 3 + 3 * n + 3 * n * n"

lemma sat_to_is_refines:
  "sat_to_is F \<le> SPEC (\<lambda>y. y = sat_is F) (\<lambda>_. sat_to_is_time (size_SAT F))"
  unfolding SPEC_def
  unfolding sat_to_is_def sat_is_unfold
      mop_list_length_def mop_set_empty_set_def add_first_part_def
      add_second_part_def
  apply(rule T_specifies_I) 
  apply(vcg' \<open>-\<close> rules: T_SPEC )
  by (auto simp: sat_to_is_time_def size_SAT_def one_enat_def)

definition "sat_to_is_space n = 9 * n + 9 * n * n"


lemma paf2: "{f l1 l2 i j |l1 l2 i j. i < k \<and> g l1 l2 i j} 
    = (\<Union>i \<in> {..<k::nat}. {f l1 l2 i j |l1 l2 j. g l1 l2 i j}) "
  by auto

lemma paf: "{f l1 l2 i |l1 l2 i. i < j \<and> g l1 l2 i} 
    = (\<Union>i \<in> {..<j::nat}. {f l1 l2 i |l1 l2. g l1 l2 i})"
  by auto 

lemma brr:
  shows "{{f l1, g l2} |l1 l2. l1 \<in> X \<and> l2 \<in> Y \<and> h l1 l2} \<subseteq> (\<Union>x \<in> X. \<Union>y \<in> Y. {{f x, g y}})"
  (is "?lhs \<subseteq> ?rhs")
proof -
  have "?lhs \<subseteq> {{f l1, g l2} |l1 l2. l1 \<in> X \<and> l2 \<in> Y}" by auto
  also have "\<dots> = (\<Union>x \<in> X. {{f x, g l2} |l2. l2 \<in> Y})" by auto
  also have "\<dots> = ?rhs" by auto
  finally show ?thesis .
qed


lemma aaa: "\<forall>x\<in>X. card x = 3 \<Longrightarrow> x\<in>X \<Longrightarrow> finite x" 
  using zero_neq_numeral by fastforce  

lemma upperbounding_card3: "\<forall>x\<in>X. card x = 3 \<Longrightarrow> x\<in>X \<Longrightarrow> y\<in>X \<Longrightarrow> 
        card {{f l1, g l2} |l1 l2. l1 \<in> x \<and> l2 \<in> y \<and> h l1 l2} \<le> 9"

      apply(rule order.trans)
       apply(rule card_mono) defer
        apply(rule brr)
       apply(rule order.trans) apply(rule card_Un) 
      subgoal apply (rule finite_imageI) using aaa by auto
       apply(rule order.trans) apply(rule sum_image_le)
      subgoal using aaa by auto
        apply simp  apply(rule order.trans)
      apply(rule sum_mono[where g="\<lambda>_. 3"]) apply simp 
        apply(rule order.trans) apply(rule card_Un)
      subgoal apply (rule finite_imageI) using aaa by auto
       apply(rule order.trans) apply(rule sum_image_le) 
      subgoal using aaa by auto
         apply simp apply simp apply simp 
      apply(rule finite_Union)
       apply (rule finite_imageI) using aaa by auto 



lemma sat_to_is_size: "size_IS (sat_is p) \<le> sat_to_is_space (size_SAT p)" 
  apply(auto simp: size_IS_def sat_is_unfold sat_to_is_space_def size_SAT_def)
  apply(rule order.trans[OF card_Un_le])
  apply(rule add_mono)
  subgoal
    apply(subst paf)
    apply(rule order.trans) apply(rule card_Un) apply simp
    apply(rule order.trans)
     apply(rule sum_image_le) apply simp
     apply simp
    apply(rule order.trans) apply(rule sum_mono[where g="(\<lambda>_. 9)"] )
    subgoal for i apply simp
      apply(rule upperbounding_card3) by auto
    apply simp
    done

  subgoal
    apply(subst paf2)
    apply(subst paf)
    apply(rule order.trans) apply(rule card_Un) apply simp
    apply(rule order.trans)
     apply(rule sum_image_le) apply simp apply simp
    apply(rule order.trans)
     apply(rule sum_mono[where g="\<lambda>_. 9 * length p"])
    subgoal apply simp
    apply(rule order.trans) apply(rule card_Un) apply simp
    apply(rule order.trans)
       apply(rule sum_image_le) apply simp apply simp
      apply(rule order.trans)
       apply(rule sum_mono[where g="\<lambda>_. 9"])
      subgoal
        apply simp apply(rule upperbounding_card3) by auto  
      apply simp done  
    subgoal apply simp done
    done
  done
  


theorem sat_to_is_ispolyred: "ispolyred sat_to_is three_cnf_sat independent_set size_SAT size_IS" 
  unfolding ispolyred_def
  apply(rule exI[where x=sat_is])
  apply(rule exI[where x=sat_to_is_time])
  apply(rule exI[where x=sat_to_is_space])
  apply(safe)
  subgoal using sat_to_is_refines by blast
  subgoal using sat_to_is_size  by blast 
  subgoal unfolding poly_def sat_to_is_time_def apply(rule exI[where x=2]) by auto
  subgoal unfolding poly_def sat_to_is_space_def apply(rule exI[where x=2]) by auto
  subgoal using is_reduction_sat_is .
  done



subsubsection \<open>Combination\<close>

theorem is_to_sc_ispolyred: 
  "ispolyred (\<lambda>a. (is_to_vc a) \<bind> vc_to_sc) independent_set set_cover size_IS size_SC"
  by(rule sat_to_is_ispolyred is_to_vc_ispolyred vc_to_sc_ispolyred  
      ispolyred_trans[OF is_to_vc_ispolyred vc_to_sc_ispolyred])


theorem sat_to_sc_ispolyred: 
  "ispolyred (\<lambda>a. (sat_to_is a \<bind> is_to_vc) \<bind> vc_to_sc) three_cnf_sat set_cover size_SAT size_SC"
  by (rule ispolyred_trans [OF ispolyred_trans
        [OF sat_to_is_ispolyred is_to_vc_ispolyred] vc_to_sc_ispolyred])

end
