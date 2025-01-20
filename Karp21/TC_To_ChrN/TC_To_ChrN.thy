theory TC_To_ChrN
  imports Main "TC_To_ChrN_Aux"
begin


subsection "Chromatic number definitions"

definition "chromaticNumber \<equiv> {(E,k). \<exists>c_Sets. is_k_colorable E k c_Sets \<and> k \<ge> 3}"

definition
  "TC_chrN E \<equiv> if (ugraph E) then ((
  {{(v1::nat,0::nat),(v2,0)}|v1 v2. {v1,v2}\<in> E} \<union>
  {{(v1,0),(0,k)}|v1 k. v1\<in> (\<Union> E) \<and> k \<in> {1..(card (\<Union>E))}} \<union>
  {{(0,k),(0,k')}|k k'. k \<in> {1..(card (\<Union>E))} \<and> k' \<in> {1..(card (\<Union>E))} \<and> k \<noteq> k'})
  ,(card (\<Union> E)+3))
else ({},0::nat)"


subsection "chromatic number lemmas"

lemma TC_chrN_edge_in_E_iff:"ugraph E \<Longrightarrow> {v1,v2} \<in> E  \<longleftrightarrow> {(v1::nat,0::nat),(v2,0)} \<in> fst(TC_chrN E)"
proof safe
  assume asms: "ugraph E" "{v1, v2} \<in> E "
  then show "{(v1, 0), (v2, 0)} \<in> fst (TC_chrN E)"
    unfolding TC_chrN_def
    by fastforce
next
  fix E v1 v2
  assume asms: "ugraph E" "{(v1, 0), (v2, 0)} \<in> fst (TC_chrN E)"
  obtain E' where E'_def2:"E' = fst (TC_chrN E)"
    by blast
  define E_nodes where E_nodes_def:
    "E_nodes = {{(v1::nat,0::nat),(v2,0)}|v1 v2. {v1,v2}\<in> E}"
  define con_nodes where con_nodes_def:
    "con_nodes = {{(v1,0),(0,k)}|v1 k. v1\<in> (\<Union> E) \<and> k \<in> {1..(card (\<Union>E))}}"
  define E'nodes where E'nodes_def:
    "E'nodes = {{(0::nat,k),(0,k')}|k k'. k \<in> {1..(card (\<Union>E))} \<and> k' \<in> {1..(card (\<Union>E))} \<and> k \<noteq> k'}"
  from asms(1) E'_def2 have E'_def: "E' = E_nodes \<union> con_nodes \<union> E'nodes"
    unfolding TC_chrN_def
    by (simp add: E_nodes_def con_nodes_def E'nodes_def)
  from E'_def2 asms(2) have v1v2inE':"{(v1, 0), (v2, 0)} \<in> E'"
    by blast
  from E'nodes_def have notin1:"{(v1, 0), (v2, 0)} \<notin> E'nodes"
    by fastforce
  have notZeroNode:"\<And>e. e\<in>con_nodes \<Longrightarrow> \<exists> a b. (a,b) \<in> e \<and> b \<noteq> 0"
    unfolding con_nodes_def
    by force
  have "\<And> a b c d. {(a, b), (c, d)} \<in> con_nodes \<Longrightarrow> b \<noteq> 0 \<or> d \<noteq> 0"
    using con_nodes_def notZeroNode
    by auto
  from this have notin2:"{(v1, 0), (v2, 0)} \<notin> con_nodes"
    by blast
  from notin1 notin2 v1v2inE' E'_def  have "{(v1, 0), (v2, 0)} \<in> E_nodes"
    by blast
  then show "{v1, v2} \<in> E"
    unfolding E_nodes_def
    by (smt doubleton_eq_iff mem_Collect_eq prod_set_simps(1))
qed

lemma nodesChromGraph:
    "(E',k) = TC_chrN E \<Longrightarrow> ugraph E \<Longrightarrow> \<Union>E' = \<Union>{{(v,0)}|v. v\<in>\<Union>E} \<union> \<Union>{{(0,n)|n. n\<in>{1..card (\<Union>E)}}}"
proof -
  fix E E' k
  assume asms:"(E',k) = TC_chrN E" "ugraph E"
  from asms have E_ugraph: "ugraph E"
    by blast
  from asms have E'_def2:"E' =
    {{(v1,0::nat),(v2,0)}|v1 v2. {v1,v2}\<in> E} \<union>
    {{(v1,0),(0,k)}|v1 k. v1\<in> (\<Union> E) \<and> k \<in> {1..(card (\<Union>E))} } \<union>
    {{(0, k), (0, k')} |k k'. k \<in> {1..card (\<Union> E)} \<and> k' \<in> {1..card (\<Union> E)} \<and> k \<noteq> k'}"
  unfolding TC_chrN_def
  by auto
  from E'_def2 have "\<Union>E' = \<Union> ({{(v1,0::nat),(v2,0)}|v1 v2. {v1,v2}\<in> E} \<union>
      {{(v1,0),(0,k)}|v1 k. v1\<in> (\<Union> E) \<and> k \<in> {1..(card (\<Union>E))} } \<union>
      {{(0, k), (0, k')} |k k'. k \<in> {1..card (\<Union> E)} \<and> k' \<in> {1..card (\<Union> E)} \<and> k \<noteq> k'})"
    by fastforce
  from E'_def2 have nodes_split1:"\<Union>E' = ( \<Union> {{(v1,0::nat),(v2,0)}|v1 v2. {v1,v2}\<in> E} \<union>
       \<Union> {{(v1,0),(0,k)}|v1 k. v1\<in> (\<Union> E) \<and> k \<in> {1..(card (\<Union>E))} } \<union>
       \<Union> {{(0, k), (0, k')} |k k'. k \<in> {1..card (\<Union> E)} \<and> k' \<in> {1..card (\<Union> E)} \<and> k \<noteq> k'})"
    by simp
  from this have nodes_split2:"\<Union> {{(v1,0),(0,k)}|v1 k. v1\<in> (\<Union> E) \<and> k \<in> {1..(card (\<Union>E))}} =
                  \<Union> {{(0,k)}|v1 k. v1\<in> (\<Union> E) \<and> k \<in> {1..(card (\<Union>E))}} \<union>
                  \<Union> {{(v1,0)}|v1 k. v1\<in> (\<Union> E) \<and> k \<in> {1..(card (\<Union>E))}}"
    by blast
  define node_split1 where node_split1_def:"node_split1= \<Union> ({{(v1,0::nat),(v2,0)}|v1 v2. {v1,v2}\<in> E})"
  define node_split2 where node_split2_def:"node_split2= \<Union> {{(0::nat,k)}|v1 k. v1\<in> (\<Union> E) \<and> k \<in> {1..(card (\<Union>E))}}"
  define node_split3 where node_split3_def:"node_split3= \<Union> {{(v1,0::nat)}|v1 k. v1\<in> (\<Union> E) \<and> k \<in> {1..(card (\<Union>E))}}"
  define node_split4 where node_split4_def:"node_split4=
            \<Union> {{(0::nat, k), (0, k')} |k k'. k \<in> {1..card (\<Union> E)} \<and> k' \<in> {1..card (\<Union> E)} \<and> k \<noteq> k'}"

  from nodes_split2 nodes_split1 have nodes_split:"\<Union>E' = node_split1 \<union>  node_split2 \<union>  node_split3 \<union>  node_split4"
    apply (simp add: node_split1_def node_split2_def node_split3_def node_split4_def)
    by auto
  have node_split_eq2':"\<Union>{{(v1,0)}|v1 k. v1\<in> (\<Union> E) \<and> k \<in> {1..(card (\<Union>E))}} =
        \<Union>{{(v1,0)}|v1. v1\<in> (\<Union> E)}"
  proof safe
    show "\<And>a b X v1 k Xa. k \<in> {1..card (\<Union> E)} \<Longrightarrow> v1 \<in> Xa \<Longrightarrow> Xa \<in> E \<Longrightarrow>
          (v1, 0) \<in> \<Union> {{(v1, 0)} |v1. v1 \<in> \<Union> E}"
      by blast
  next
    fix e
    fix v
    assume asms: "v\<in> e" "e: E"
    from asms(2) have "card e = 2"
      using E_ugraph
      unfolding ugraph_def
      by blast
    from this asms(2) have "card (\<Union> E) \<noteq> 0"
      by (metis E_ugraph Sup_upper card.infinite card_mono finite_Union
          not_numeral_le_zero ugraph_def zero_neq_numeral)
    from this asms show "(v, 0) \<in> \<Union> {u. \<exists>v1 k. u = {(v1, 0)} \<and> v1 \<in> \<Union> E \<and> k \<in> {1..card (\<Union> E)}}"
      using Icc_eq_insert_lb_nat by auto
  qed
  have node_split_eq3':"\<Union> {{(v1,0::nat),(v2,0)}|v1 v2. {v1,v2}\<in> E} = \<Union>{{(v,0::nat)}|v. v\<in>\<Union>E}"
  proof safe
    show "\<And>a b X v1 v2. {v1, v2} \<in> E \<Longrightarrow> (v1, 0) \<in> \<Union> {{(v, 0)} |v. v \<in> \<Union> E}" by blast
  next
    show "\<And>a b X v1 v2. {v1, v2} \<in> E \<Longrightarrow> (v2, 0) \<in> \<Union> {{(v, 0)} |v. v \<in> \<Union> E}" by blast
  next
    fix e
    fix v
    assume asms:"e \<in> E" "v\<in>e"
    from E_ugraph asms(1) have "card e = 2"
      unfolding ugraph_def
      by blast
    from this obtain v' where "e = {v, v'}"
      by (metis asms(2) card_2_iff doubleton_eq_iff insertE singleton_iff)
    from this asms(1) have "{v,v'} \<in> E"
      by blast
    from this show "(v, 0) \<in> \<Union> {{(v1, 0), (v2, 0)} |v1 v2. {v1, v2} \<in> E}"
      by blast
  qed
  have node_split_eq4':"\<Union> {{(0, k), (0, k')} |k k'. k \<in> {1..card (\<Union> E)} \<and> k' \<in> {1..card (\<Union> E)} \<and> k \<noteq> k'} =
        \<Union>{{(0,n)|n. n\<in>{1..card (\<Union>E)}}}"
  proof safe
    show "\<And>a b X k k'.
       k \<in> {1..card (\<Union> E)} \<Longrightarrow> k' \<in> {1..card (\<Union> E)} \<Longrightarrow> k \<noteq> k' \<Longrightarrow> (0, k) \<in> \<Union> {{(0, n) |n. n \<in> {1..card (\<Union> E)}}}"
      by blast
  next
    show "\<And>a b X k k'.
       k \<in> {1..card (\<Union> E)} \<Longrightarrow> k' \<in> {1..card (\<Union> E)} \<Longrightarrow> k \<noteq> k' \<Longrightarrow> (0, k') \<in> \<Union> {{(0, n) |n. n \<in> {1..card (\<Union> E)}}}"
      by blast
  next
    fix n ::nat
    assume asms:" n \<in> {1..card (\<Union> E)}"
    from this have asm1:"1 \<le> n"
      by simp
    from asms have asm2:"n\<le>card (\<Union> E)"
      by simp
    from asm1 asm2 have card1:"1 \<le> card (\<Union> E)"
      by linarith
    from this obtain e where e_def: "e\<in> E"
      by fastforce
    from this E_ugraph have "card e = 2"
      unfolding ugraph_def
      by blast
    from this e_def card1 have  "2 \<le> card (\<Union> E)"
      by (metis One_nat_def Suc_le_eq Union_upper card_ge_0_finite card_mono)
    from this obtain n'::"nat" where "n'\<in> {1..card (\<Union> E)} \<and> n \<noteq> n'"
      by (metis atLeastAtMost_iff card1 numeral_le_one_iff order_refl semiring_norm(69))
    from this asms show "(0, n) \<in> \<Union> {{(0, k), (0, k')} |k k'. k \<in> {1..card (\<Union> E)} \<and>
                                                         k' \<in> {1..card (\<Union> E)} \<and> k \<noteq> k'}"
      by blast
  qed
  have node_split_eq1:"node_split2 =
                  \<Union> {{(0,k)}|k. k \<in> {1..(card (\<Union>E))}}"
    apply (simp add: node_split2_def)
    by (metis (mono_tags, opaque_lifting) Sup_bot_conv(2)
        all_not_in_conv card.empty not_less_eq_eq)
  from node_split_eq2' have node_split_eq2: "node_split3 = \<Union>{{(v,0)}|v. v\<in> (\<Union> E)}"
    by (simp add: node_split3_def)
  from node_split_eq3' have node_split_eq3: "node_split1 = \<Union>{{(v,0::nat)}|v. v\<in>\<Union>E}"
    by (simp add: node_split1_def)
  from node_split_eq4' have node_split_eq4:"node_split4 = \<Union>{{(0,n)|n. n\<in>{1..card (\<Union>E)}}}"
    by (simp add: node_split4_def)
  from node_split_eq1 node_split_eq2 node_split_eq3 node_split_eq4 nodes_split have node_split_eq5:
    "\<Union>E' = \<Union>{{(v,0)}|v. v\<in>\<Union>E} \<union> \<Union>{{(0,n)|n. n\<in>{1..card (\<Union>E)}}}"
    by auto
  from this show "\<Union> E' = \<Union> {{(v, 0)} |v. v \<in> \<Union> E} \<union> \<Union> {{(0, n) |n. n \<in> {1..card (\<Union> E)}}}"
    by blast
qed


subsection "Three colorability to chromatic number"

lemma threeColToChroN:"\<And>E. E \<in> three_colorability \<Longrightarrow> TC_chrN E \<in> chromaticNumber"
proof -
  fix E :: "nat set set"
  assume asms:"E \<in> three_colorability"
  from asms obtain c1 c2 c3 where c_Sets_def:"is_k_colorable E 3 {c1,c2,c3} \<and> c1 \<noteq> c2  \<and> c1 \<noteq> c3  \<and> c2 \<noteq> c3 "
    unfolding three_colorability_def
    by (smt card_dif_elements choice3 insert_commute is_k_colorable_def mem_Collect_eq)
  from asms have E_ugraph:"ugraph E"
    unfolding three_colorability_def is_k_colorable_def is_colorable_def
    by blast
  obtain E' k where E'_def:"(E', k) = TC_chrN E"
    by (metis surj_pair)
  from E'_def E_ugraph have E'_def2:"E' =
      {{(v1,0::nat),(v2,0)}|v1 v2. {v1,v2}\<in> E} \<union>
      {{(v1,0),(0,k)}|v1 k. v1\<in> (\<Union> E) \<and> k \<in> {1..(card (\<Union>E))} } \<union>
      {{(0, k), (0, k')} |k k'. k \<in> {1..card (\<Union> E)} \<and> k' \<in> {1..card (\<Union> E)} \<and> k \<noteq> k'}"
    unfolding TC_chrN_def
    by auto
  from E'_def E_ugraph have k_def:"k = (card (\<Union> E)+3)"
    unfolding TC_chrN_def
    by simp

  from E'_def2 E_ugraph have E'_ugraph:"ugraph E'"

  proof -
    from E'_def2 E_ugraph have "finite E'"
      unfolding ugraph_def
      using chromatik_finite1 chromatik_finite2 chromatik_finite3
      by (smt E'_def E_ugraph card_eq_0_iff finite_UnI finite_Union
          prod.inject TC_chrN_def zero_neq_numeral)
    moreover from E'_def2 E_ugraph have "(\<forall>e\<in>{{(v1::nat, 0::nat), (v2, 0)} |v1 v2. {v1, v2} \<in> E}. card e = 2)"
      using chromatik_card2
      by blast
    moreover from E'_def2 E_ugraph have "(\<forall>e\<in>{{(v1, 0), (0, k)} |v1 k. v1 \<in> \<Union> E \<and> k \<in> {1..card (\<Union> E)}}. card e = 2)"
      by force
    ultimately show "ugraph E'"
      unfolding ugraph_def
      by (auto simp: E'_def2)
  qed

  obtain c_Sets' where c_Sets'_def: "c_Sets'={\<Union>{{(v,0)}|v. v:c1} , \<Union>{{(v,0)}|v. v:c2} , \<Union>{{(v,0)}|v. v:c3}}
                                            \<union> {{(0,n)}|n. n \<in> {1..card (\<Union> E)}}"
    by blast

  from E'_def E_ugraph have node_split_eq5:
    "\<Union>E' = \<Union>{{(v,0)}|v. v\<in>\<Union>E} \<union> \<Union>{{(0,n)|n. n\<in>{1..card (\<Union>E)}}}"
    using nodesChromGraph
    by presburger

  have node_split_eq6:"\<Union>{{(v,0::nat)}|v. v\<in>\<Union>E} =
    \<Union>{\<Union> {{(v, 0::nat)} |v. v \<in> c1}, \<Union> {{(v, 0)} |v. v \<in> c2}, \<Union> {{(v, 0)} |v. v \<in> c3}}"
  proof -
    define step1 where step1_def:"step1= \<Union> {{(v, 0::nat)} |v. v \<in> \<Union> E}"
    define step2 where step2_def:"step2= \<Union>({{(v,0::nat)}|v. v\<in>c1 \<or> v\<in> c2 \<or> v\<in> c3 })"
    define step3 where step3_def:"step3= \<Union> {\<Union> {{(v, 0::nat)} |v. v \<in> c1},
                                            \<Union> {{(v, 0)} |v. v \<in> c2},
                                            \<Union> {{(v, 0)} |v. v \<in> c3}}"
    from c_Sets_def have "\<Union>E = \<Union>{c1,c2,c3}"
      unfolding is_k_colorable_def is_colorable_def
      by linarith
    from this step2_def step1_def have step1:"step1 =step2"
      by auto
    have "\<Union>({{(v,0)}|v. v\<in>c1 \<or> v\<in> c2 \<or> v\<in> c3 }) =
                    \<Union>{\<Union> {{(v, 0::nat)} |v. v \<in> c1}, \<Union> {{(v, 0)} |v. v \<in> c2}, \<Union> {{(v, 0)} |v. v \<in> c3}}"
      by blast
    from this step2_def step3_def have step2:"step2 = step3"
      by simp
    from step1 step2 have "step1 = step3"
      by simp
    from this show ?thesis
      by (simp add: step1_def step3_def)
  qed

  from node_split_eq5 node_split_eq6 c_Sets'_def have c_Sets'_complete:"\<Union>E' = \<Union>c_Sets'"
  proof -
    define step1 where step1_def:"step1= \<Union>{{(v,0::nat)}|v. v\<in>\<Union>E}"
    define step2 where step2_def:"step2= \<Union>{{(0::nat,n)|n. n\<in>{1..card (\<Union>E)}}}"
    define step3 where step3_def:"step3= \<Union>{\<Union> {{(v, 0::nat)} |v. v \<in> c1}, \<Union> {{(v, 0)} |v. v \<in> c2},
                                            \<Union> {{(v, 0)} |v. v \<in> c3}}"
    from node_split_eq5 have E'eq:
      "\<Union>E' =step1 \<union> step2"
      by (simp add: step1_def step2_def)
    from node_split_eq6 have "step1 =  step3"
       by (simp add: step1_def step3_def)
    from E'eq this have "\<Union>E' = step3 \<union> step2"
      by fast
    from this show ?thesis
      apply (simp add: step2_def step3_def c_Sets'_def)
      by blast
  qed

  have EgraphE'nodesdisjoint:"{\<Union>{{(v,0)}|v. v:c1} , \<Union>{{(v,0)}|v. v:c2} , \<Union>{{(v,0)}|v. v:c3}}
                                            \<inter> {{(0,n)}|n. n \<in> {1..card (\<Union> E)}} = {}"
    by fastforce

  from c_Sets_def have c1c2_empty:"c1\<inter> c2 = {}"
    unfolding is_k_colorable_def is_colorable_def
    by auto

  from c_Sets_def have c1c3_empty:"c1\<inter> c3 = {}"
    unfolding is_k_colorable_def is_colorable_def
    by auto

  from c_Sets_def have c2c3_empty:"c2\<inter> c3 = {}"
    unfolding is_k_colorable_def is_colorable_def
    by auto

  from c1c2_empty have c1c2_empty':"\<Union>{{(v,0)}|v. v:c1} \<inter> \<Union>{{(v,0)}|v. v:c2} = {}"
    by auto

  from c1c3_empty have c1c3_empty':"\<Union>{{(v,0)}|v. v:c1} \<inter> \<Union>{{(v,0)}|v. v:c3} = {}"
    by auto

  from c2c3_empty have c2c3_empty':"\<Union>{{(v,0)}|v. v:c2} \<inter> \<Union>{{(v,0)}|v. v:c3} = {}"
    by auto

  have c1E'nodes_empty':"\<Union>{{(v,0)}|v. v:c1} \<inter> \<Union>{{(0,n)}|n. n \<in> {1..card (\<Union> E)}} = {}"
    by auto

  have c2E'nodes_empty':"\<Union>{{(v,0)}|v. v:c2} \<inter> \<Union>{{(0,n)}|n. n \<in> {1..card (\<Union> E)}} = {}"
    by auto

  have c3E'nodes_empty':"\<Union>{{(v,0)}|v. v:c3} \<inter> \<Union>{{(0,n)}|n. n \<in> {1..card (\<Union> E)}} = {}"
    by auto

  from c1c2_empty' c1c3_empty' c1E'nodes_empty' c1c3_empty have c1Csets_empty:
    "\<forall>c\<in>c_Sets'. c \<noteq> \<Union> {{(v, 0)} |v. v \<in> c1} \<longrightarrow> c \<inter> \<Union> {{(v, 0)} |v. v \<in> c1} = {}"
    by (auto simp: c_Sets'_def)

  from c1c2_empty' c2c3_empty' c2E'nodes_empty' c2c3_empty have c2Csets_empty:
    "\<forall>c\<in>c_Sets'. c \<noteq> \<Union> {{(v, 0)} |v. v \<in> c2} \<longrightarrow> c \<inter> \<Union> {{(v, 0)} |v. v \<in> c2} = {}"
    by (auto simp: c_Sets'_def)

  from c1c3_empty' c2c3_empty' c3E'nodes_empty' c2c3_empty have c3Csets_empty:
    "\<forall>c\<in>c_Sets'. c \<noteq> \<Union> {{(v, 0)} |v. v \<in> c3} \<longrightarrow> c \<inter> \<Union> {{(v, 0)} |v. v \<in> c3} = {}"
    by (auto simp: c_Sets'_def)

  have E'nodesCsets_empty:
    "\<forall>c\<in>c_Sets'. \<forall>c'\<in>{{(0,n)}|n. n \<in> {1..card (\<Union> E)}}. c \<noteq> c' \<longrightarrow> c \<inter> c' = {}"
    by (auto simp: c_Sets'_def)

  from c1Csets_empty c2Csets_empty c3Csets_empty E'nodesCsets_empty have color_disjoint:
    "\<forall>c\<in>c_Sets'. \<forall>c'\<in>c_Sets'. c \<noteq> c' \<longrightarrow> c \<inter> c' = {}"
    by (auto simp: c_Sets'_def)


  from E'_def have "E' = fst (TC_chrN E)"
    by (metis fst_conv)

  from this E_ugraph have edge_preserve:"\<forall> v1 v2. {v1,v2} \<in> E  \<longleftrightarrow> {(v1::nat,0::nat),(v2,0)} \<in>E'"
    using TC_chrN_edge_in_E_iff[where E = E]
    by auto


  from c_Sets_def have "\<forall>v\<in>c1. \<forall>v'\<in>c1. {v, v'} \<notin> E"
    unfolding is_k_colorable_def is_colorable_def
    by simp

  from this edge_preserve have c1'sound:"\<forall>v\<in>\<Union> {{(v, 0)} |v. v \<in> c1}. \<forall>v'\<in>\<Union> {{(v, 0)} |v. v \<in> c1}. {v, v'} \<notin> E'"
    by blast

  from c_Sets_def have "\<forall>v\<in>c2. \<forall>v'\<in>c2. {v, v'} \<notin> E"
    unfolding is_k_colorable_def is_colorable_def
    by simp

  from this edge_preserve have c2'sound:"\<forall>v\<in>\<Union> {{(v, 0)} |v. v \<in> c2}. \<forall>v'\<in>\<Union> {{(v, 0)} |v. v \<in> c2}. {v, v'} \<notin> E'"
    by blast

  from c_Sets_def have "\<forall>v\<in>c3. \<forall>v'\<in>c3. {v, v'} \<notin> E"
    unfolding is_k_colorable_def is_colorable_def
    by simp

  from this edge_preserve have c3'sound:"\<forall>v\<in>\<Union> {{(v, 0)} |v. v \<in> c3}. \<forall>v'\<in>\<Union> {{(v, 0)} |v. v \<in> c3}. {v, v'} \<notin> E'"
    by blast

  from E'_ugraph have E'nodes_sound:"\<forall>c\<in>{{(0,n)}|n. n \<in> {1..card (\<Union> E)}}. \<forall>v\<in>c. \<forall>v'\<in>c. {v, v'} \<notin> E'"
    unfolding ugraph_def
    by auto


  from c1'sound c2'sound c3'sound E'nodes_sound have c_Sets_sound:"\<forall>c\<in>c_Sets'. \<forall>v\<in>c. \<forall>v'\<in>c. {v, v'} \<notin> E'"
    by (simp add: c_Sets'_def)



  have c_Sets'fin1:"finite {\<Union>{{(v,0)}|v. v:c1} , \<Union>{{(v,0)}|v. v:c2} , \<Union>{{(v,0)}|v. v:c3}}"
    by blast

  have c_Sets'fin2:"finite {{(0,n)}|n. n \<in> {1..card (\<Union> E)}}"
    by simp


  from EgraphE'nodesdisjoint c_Sets'fin1 c_Sets'fin2 c_Sets'_def have c_Sets'_split:
                      "card c_Sets' =
                       card {\<Union>{{(v,0::nat)}|v. v:c1} , \<Union>{{(v,0)}|v. v:c2} , \<Union>{{(v,0)}|v. v:c3}} +
                       card {{(0::nat,n)}|n. n \<in> {1..card (\<Union> E)}}"
    using card_Un_disjoint [where A = "{\<Union>{{(v,0::nat)}|v. v:c1} , \<Union>{{(v,0)}|v. v:c2} , \<Union>{{(v,0)}|v. v:c3}}"
                              and B = "{{(0::nat,n)}|n. n \<in> {1..card (\<Union> E)}}"]
    by blast

  from c_Sets_def have c1c2_noteq:"c1 \<noteq> c2"
    by blast

  from c_Sets_def have c1c3_noteq:"c1 \<noteq> c3"
    by blast

  from c_Sets_def have c2c3_noteq:"c2 \<noteq> c3"
    by blast


  from this have c1'c2'_noteq:"\<Union>{{(v,0::nat)}|v. v:c1} \<noteq> \<Union>{{(v,0::nat)}|v. v:c2}"
  proof (cases "c1 = {}")
    case True
    from this c1c2_noteq have "c2 \<noteq> {}"
      by blast
    from this True obtain v where "v\<in>c2 \<and> v \<notin> c1"
      by blast
    from this have "(v,0::nat) \<notin> \<Union> {{(v, 0::nat)} |v. v \<in> c1} \<and>
                    (v,0::nat) \<in> \<Union> {{(v, 0::nat)} |v. v \<in> c2}"
      by blast
    then show ?thesis
      by metis
  next
    case False
    from this obtain v where "v\<in>c1 \<and> v \<notin> c2"
      using c1c2_empty by auto
    from this have "(v,0::nat) \<in> \<Union> {{(v, 0::nat)} |v. v \<in> c1} \<and>
                    (v,0::nat) \<notin> \<Union> {{(v, 0::nat)} |v. v \<in> c2}"
      by blast
    then show ?thesis
      by metis
  qed

from this have c1'c3'_noteq:"\<Union>{{(v,0::nat)}|v. v:c1} \<noteq> \<Union>{{(v,0::nat)}|v. v:c3}"
  proof (cases "c1 = {}")
    case True
    from this c1c3_noteq have "c3 \<noteq> {}"
      by blast
    from this True obtain v where "v\<in>c3 \<and> v \<notin> c1"
      by blast
    from this have "(v,0::nat) \<notin> \<Union> {{(v, 0::nat)} |v. v \<in> c1} \<and>
                    (v,0::nat) \<in> \<Union> {{(v, 0::nat)} |v. v \<in> c3}"
      by blast
    then show ?thesis
      by metis
  next
    case False
    from this obtain v where "v\<in>c1 \<and> v \<notin> c3"
      using c1c3_empty by auto
    from this have "(v,0::nat) \<in> \<Union> {{(v, 0::nat)} |v. v \<in> c1} \<and>
                    (v,0::nat) \<notin> \<Union> {{(v, 0::nat)} |v. v \<in> c3}"
      by blast
    then show ?thesis
      by metis
  qed

from this have c2'c3'_noteq:"\<Union>{{(v,0::nat)}|v. v:c2} \<noteq> \<Union>{{(v,0::nat)}|v. v:c3}"
  proof (cases "c2 = {}")
    case True
    from this c2c3_noteq have "c3 \<noteq> {}"
      by blast
    from this True obtain v where "v\<in>c3 \<and> v \<notin> c2"
      by blast
    from this have "(v,0::nat) \<notin> \<Union> {{(v, 0::nat)} |v. v \<in> c2} \<and>
                    (v,0::nat) \<in> \<Union> {{(v, 0::nat)} |v. v \<in> c3}"
      by blast
    then show ?thesis
      by metis
  next
    case False
    from this obtain v where "v\<in>c2 \<and> v \<notin> c3"
      using c2c3_empty by auto
    from this have "(v,0::nat) \<in> \<Union> {{(v, 0::nat)} |v. v \<in> c2} \<and>
                    (v,0::nat) \<notin> \<Union> {{(v, 0::nat)} |v. v \<in> c3}"
      by blast
    then show ?thesis
      by metis
  qed
  from c1'c2'_noteq c1'c3'_noteq c2'c3'_noteq have card_c_Sets1:
    "card {\<Union>{{(v,0::nat)}|v. v:c1} , \<Union>{{(v,0)}|v. v:c2} , \<Union>{{(v,0)}|v. v:c3}} = 3"
    by auto

  have card_c_Sets2:"card {{(0::nat, n)} |n. n \<in> {1..card (\<Union> E)}} = card (\<Union> E)"
    using card_additional_nodes[where x= "card (\<Union>E)"]
    by blast

  from card_c_Sets1 card_c_Sets2 c_Sets'_split have k_card: "card c_Sets' = k"
    by (simp add:  k_def c_Sets'_def)

  from k_def have kgreaterThr:"3 \<le> k"
    by simp

  from E'_def have "(E', k) \<in> chromaticNumber"
    unfolding chromaticNumber_def is_k_colorable_def is_colorable_def
    using c_Sets'_complete E'_ugraph color_disjoint c_Sets_sound k_card kgreaterThr
    by blast
  from this E'_def show "TC_chrN E \<in> chromaticNumber"
    by simp
qed


lemma chroNToThreeCol_ugraph:"\<And>E. ugraph E \<Longrightarrow> TC_chrN E \<in> chromaticNumber \<Longrightarrow> E \<in> three_colorability"
proof -
  fix E :: "nat set set"
  assume asms:"TC_chrN E \<in> chromaticNumber" "ugraph E"
  obtain E' k  where E'def_2:"(E',k)=TC_chrN E"
    by (metis surj_pair)
  from this asms have E'chrN:"(E',k) \<in> chromaticNumber"
    by simp
  from E'def_2 have E'_def_3:"fst (TC_chrN E) = E'"
    by (metis fstI)


  from E'def_2 asms have E'_def: "E' =
      {{(v1::nat,0::nat),(v2,0)}|v1 v2. {v1,v2}\<in> E} \<union>
      {{(v1,0),(0,k)}|v1 k. v1\<in> (\<Union> E) \<and> k \<in> {1..(card (\<Union>E))}} \<union>
      {{(0,k),(0,k')}|k k'. k \<in> {1..(card (\<Union>E))} \<and> k' \<in> {1..(card (\<Union>E))} \<and> k \<noteq> k'}"
    unfolding TC_chrN_def
    by simp
  from E'def_2 asms have k_def: "k =card (\<Union> E)+3"
    unfolding TC_chrN_def
    by simp
  from E'chrN obtain c_Sets' where c_Sets'_def:"is_k_colorable E' k c_Sets'"
    unfolding chromaticNumber_def
    by blast

  from c_Sets'_def k_def have c_Sets'_card:"card c_Sets' = card (\<Union> E)+3"
    unfolding is_k_colorable_def
    by blast

  from this have c_Sets'fin:"finite c_Sets'"
    using card.infinite by fastforce

  from c_Sets'_def have c_Sets'_complete:"\<Union>c_Sets' = \<Union>E'"
    unfolding is_k_colorable_def is_colorable_def
    by argo

  define E_nodes where E_nodes_def:"E_nodes = \<Union>{{(v,0::nat)}|v. v\<in>\<Union>E}"

  define E'_nodes where E'_nodes_def:"E'_nodes = \<Union>{{(0::nat,n)|n. n\<in>{1..card (\<Union>E)}}}"

  from E'def_2 asms(2) E_nodes_def E'_nodes_def have node_split_eq:
    "\<Union>E' = E_nodes \<union> E'_nodes"
    using nodesChromGraph
    by presburger


  from E_nodes_def E'_nodes_def have E'disjointparts: "E_nodes \<inter> E'_nodes = {}"
    by auto



  from this have E'nodesOwnColor:"\<And>v. v \<in> {(0,n)|n. n\<in>{1..card (\<Union>E)}} \<Longrightarrow> {v}\<in> c_Sets'"
  proof -
    fix v
    assume asms: "v \<in> {(0::nat,n)|n. n\<in>{1..card (\<Union>E)}}"
    from asms obtain n where n_def:"v = (0::nat,n) \<and> 1 \<le> n \<and> n \<le> card(\<Union>E)"
      by auto
    show "{v} \<in> c_Sets'"
    proof (cases "{v} \<in> c_Sets'")
      case True
      then show ?thesis by simp
    next
      case F1:False
      from asms c_Sets'_complete node_split_eq have "v\<in> \<Union>c_Sets'"
        by (simp add: E_nodes_def E'_nodes_def)
      from this F1 obtain color v' where color_def:"color \<in> c_Sets' \<and> v\<in> color \<and> v' \<in> color \<and> v\<noteq> v'"
        by (metis UnionE ex_in_conv insertCI mk_disjoint_insert)
      from color_def c_Sets'_complete have v'inE':"v' \<in> \<Union>E'"
        by blast
      from color_def c_Sets'_def have color_sound:"\<forall>v1\<in>color. \<forall>v2\<in>color. {v1,v2}\<notin> E'"
        unfolding is_k_colorable_def is_colorable_def
        by meson
      from this color_def have vv'notinE':"{v,v'}\<notin> E'"
        by blast
      then show ?thesis
      proof (cases "v' \<in> \<Union>{{(v,0)}|v. v\<in>\<Union>E}")
        case True
        from this asms E'_def have "{v,v'}\<in> E'"
          by auto
        from this vv'notinE' show ?thesis
          by simp
      next
        case False
        from this v'inE' node_split_eq have "v' \<in> \<Union>{{(0,n)|n. n\<in>{1..card (\<Union>E)}}}"
          by (auto simp: E_nodes_def E'_nodes_def)
        from this asms E'_def color_def have "{v,v'}\<in> E'"
          by blast
        from this vv'notinE' show ?thesis by simp
      qed
    qed
  qed

  from this have "{{(0, n)} |n. n \<in> {1..card (\<Union> E)}} \<subseteq> c_Sets'"
    by blast

  from this obtain E_colors where E_colors_def:"E_colors \<union> {{(0::nat, n)} |n. n \<in> {1..card (\<Union> E)}} = c_Sets' \<and>
                                                E_colors \<inter> {{(0::nat, n)} |n. n \<in> {1..card (\<Union> E)}} = {}"
    by auto

  from E_colors_def c_Sets'fin have fin1:"finite E_colors"
    by blast
  from E_colors_def c_Sets'fin have fin2:"finite {{(0, n)} |n. n \<in> {1..card (\<Union> E)}}"
    by simp

  from E_colors_def fin1 fin2  have c_Sets'_card_split:
    "card c_Sets' = card E_colors + card {{(0::nat, n)} |n. n \<in> {1..card (\<Union> E)}}"
    using card_Un_disjoint[where A= E_colors and B = "{{(0::nat, n)} |n. n \<in> {1..card (\<Union> E)}}" ]
    by blast

  have card_c_Sets2:"card {{(0::nat, n)} |n. n \<in> {1..card (\<Union> E)}} = card (\<Union> E)"
    using card_additional_nodes[where x= "card (\<Union>E)"]
    by blast

  from this c_Sets'_card c_Sets'_card_split have "card E_colors = 3"
    by linarith

  from this obtain c1' c2' c3' where E_colors_def':
    "E_colors = {c1',c2',c3'} \<and> c1' \<noteq> c2' \<and> c1' \<noteq> c3' \<and> c2' \<noteq> c3'"
    using choice3
    by (metis (no_types, lifting) card_dif_elements insert_commute)

  from this E_colors_def have E_color_in_c_Sets': "c1' \<in> c_Sets' \<and> c2' \<in> c_Sets' \<and> c3' \<in> c_Sets'"
    by blast

  from E_colors_def' E_color_in_c_Sets' c_Sets'_def  have c1'c2'disjoint:"c1' \<inter>  c2' = {}"
    unfolding is_k_colorable_def is_colorable_def
    by auto

  from E_colors_def' E_color_in_c_Sets' c_Sets'_def  have c1'c3'disjoint:"c1' \<inter>  c3' = {}"
    unfolding is_k_colorable_def is_colorable_def
    by auto

  from E_colors_def' E_color_in_c_Sets' c_Sets'_def  have c2'c3'disjoint:"c2' \<inter>  c3' = {}"
    unfolding is_k_colorable_def is_colorable_def
    by auto

  from E_color_in_c_Sets' c_Sets'_def  have c1'_color:"\<forall>v\<in>c1'. \<forall>v'\<in>c1'. {v, v'} \<notin> E'"
    unfolding is_k_colorable_def is_colorable_def
    by meson

  from E_color_in_c_Sets' c_Sets'_def  have c2'_color:"\<forall>v\<in>c2'. \<forall>v'\<in>c2'. {v, v'} \<notin> E'"
    unfolding is_k_colorable_def is_colorable_def
    by meson

  from E_color_in_c_Sets' c_Sets'_def  have c3'_color:"\<forall>v\<in>c3'. \<forall>v'\<in>c3'. {v, v'} \<notin> E'"
    unfolding is_k_colorable_def is_colorable_def
    by meson

  from E_colors_def E'_nodes_def have c_Sets'unioneq:"\<Union>c_Sets' = \<Union>E_colors \<union> E'_nodes"
    by blast

  have "\<And>v. v\<in> \<Union>E_colors \<Longrightarrow> v \<notin>E'_nodes"
  proof -
    fix v
    assume asms: "v\<in> \<Union>E_colors"
    show "v \<notin>E'_nodes"
    proof (cases "v \<notin>E'_nodes")
      case True
      then show ?thesis
        by blast
    next
      case F1:False
      from this have "v \<in> E'_nodes"
        by blast
      from this E'_nodes_def obtain c1 where c1_def:"v \<in> c1 \<and> c1\<in> {{(0, n)} |n. n \<in> {1..card (\<Union> E)}}"
        by blast
      from asms obtain c2 where c2_def:"v \<in> c2 \<and> c2\<in> E_colors"
        by blast
      from E_colors_def c1_def c2_def have c1c2noteq:"c1 \<noteq> c2"
        by blast
      from E_colors_def c1_def c2_def have "c1\<in> c_Sets' \<and> c2\<in> c_Sets'"
        by blast
      from this c_Sets'_def c1c2noteq have "c1\<inter> c2 = {}"
        unfolding is_k_colorable_def is_colorable_def
        by meson
      from this c1_def c2_def have "False"
        by blast
      then show ?thesis
        by blast
    qed
  qed

  from this have E_colorNodesDisjoint:"\<Union>E_colors \<inter> E'_nodes = {}"
    by blast
  from node_split_eq c_Sets'_complete c_Sets'unioneq have
    " E_nodes \<union> E'_nodes =
      \<Union> E_colors \<union> E'_nodes"
    by argo
  from this E_colorNodesDisjoint E'disjointparts have "\<Union>E_colors = E_nodes "
    by auto


  from this E_colors_def' have colorseteqnodes:"c1'\<union>c2'\<union>c3' =E_nodes"
    by auto


  from colorseteqnodes have c1'subset:"c1' \<subseteq> E_nodes"
    by blast

  from colorseteqnodes have c2'subset:"c2' \<subseteq> E_nodes"
    by blast

  from colorseteqnodes have c3'subset:"c3' \<subseteq> E_nodes"
    by blast

  obtain c1 where c1_def:"c1= \<Union>{{v}|v. (v,0)\<in> c1'}"
    by blast

  obtain c2 where c2_def:"c2= \<Union>{{v}|v. (v,0)\<in> c2'}"
    by blast

  obtain c3 where c3_def:"c3= \<Union>{{v}|v. (v,0)\<in> c3'}"
    by blast


  from c1_def c2_def E_colors_def' have c1c2Noteq:"c1 \<noteq> c2"
  proof (cases "c1= {}")
    case T:True
    from this  c1_def c1'subset E_nodes_def have "c1' = {}"
      by blast
    from this E_colors_def' have "c2' \<noteq> {}"
      by blast
    from this c2'subset E_nodes_def obtain v where "(v,0::nat)\<in> c2' \<and> v\<in>\<Union>E"
      by blast
    from this c2_def have "v\<in> c2"
      by blast
    from this T show ?thesis
      by blast
  next
    case False
    from this c1_def c1'subset E_nodes_def have "c1' \<noteq> {}"
      by blast
    from this c1'subset E_nodes_def c1'c2'disjoint obtain v where "(v,0::nat)\<in> c1' \<and> (v,0)\<notin> c2' \<and> v\<in>\<Union>E"
      by blast
    from this c1_def c2_def have "v\<in> c1 \<and> v \<notin> c2"
      by blast
    then show ?thesis
      by blast
  qed

    from c1_def c2_def E_colors_def' have c1c3Noteq:"c1 \<noteq> c3"
  proof (cases "c1= {}")
    case T:True
    from this  c1_def c1'subset E_nodes_def have "c1' = {}"
      by blast
    from this E_colors_def' have "c3' \<noteq> {}"
      by blast
    from this c3'subset E_nodes_def obtain v where "(v,0::nat)\<in> c3' \<and> v\<in>\<Union>E"
      by blast
    from this c3_def have "v\<in> c3"
      by blast
    from this T show ?thesis
      by blast
  next
    case False
    from this c1_def c1'subset E_nodes_def have "c1' \<noteq> {}"
      by blast
    from this c1'subset E_nodes_def c1'c3'disjoint obtain v where "(v,0::nat)\<in> c1' \<and> (v,0)\<notin> c3' \<and> v\<in>\<Union>E"
      by blast
    from this c1_def c3_def have "v\<in> c1 \<and> v \<notin> c3"
      by blast
    then show ?thesis
      by blast
  qed

    from c1_def c2_def E_colors_def' have c2c3Noteq:"c2 \<noteq> c3"
  proof (cases "c2= {}")
    case T:True
    from this  c2_def c2'subset E_nodes_def have "c2' = {}"
      by blast
    from this E_colors_def' have "c3' \<noteq> {}"
      by blast
    from this c3'subset E_nodes_def obtain v where "(v,0::nat)\<in> c3' \<and> v\<in>\<Union>E"
      by blast
    from this c3_def have "v\<in> c3"
      by blast
    from this T show ?thesis
      by blast
  next
    case False
    from this c2_def c2'subset E_nodes_def have "c2' \<noteq> {}"
      by blast
    from this c2'subset E_nodes_def c2'c3'disjoint obtain v where "(v,0::nat)\<in> c2' \<and> (v,0)\<notin> c3' \<and> v\<in>\<Union>E"
      by blast
    from this c2_def c3_def have "v\<in> c2 \<and> v \<notin> c3"
      by blast
    then show ?thesis
      by blast
  qed


  from c1c2Noteq c1c3Noteq c2c3Noteq have colorNoteq:"c1 \<noteq> c2 \<and> c1 \<noteq> c3 \<and> c2 \<noteq> c3"
    by blast

  have color_complete:"\<Union> E = \<Union> {c1, c2, c3}"
  proof -
    define step1 where step1_def:
      "step1 = \<Union> ({{v} |v. (v, 0) \<in> c1'} \<union> {{v} |v. (v, 0) \<in> c2'} \<union>  {{v} |v. (v, 0) \<in> c3'})"
    define step2 where step2_def:
      "step2 = \<Union>({{v} |v. (v, 0) \<in> c1' \<or>  (v, 0) \<in> c2' \<or>  (v, 0) \<in> c3' })"
    define step3 where step3_def:
      "step3 = \<Union>({{v} |v. (v, 0) \<in> E_nodes })"

    have "\<Union> {c1, c2, c3} = c1 \<union> c2 \<union> c3"
      by force
    from this c1_def c2_def c3_def have st1:
        "\<Union> {c1, c2, c3} =
        step1"
      by (auto simp: step1_def)
    from step1_def step2_def have st2:
      " step1 =  step2"
      by blast
    from colorseteqnodes step2_def step3_def have st3:"step2 = step3"
      by blast
    from E_nodes_def step3_def have st4:"step3 = \<Union>E"
      by blast
    from st1 st2 st3 st4 show ?thesis
      by argo
  qed

  from c1_def c2_def c1'c2'disjoint have c1c2disjoint: "c1 \<inter> c2 ={}"
    by blast
  from c1_def c3_def c1'c3'disjoint have c1c3disjoint: "c1 \<inter> c3 ={}"
    by blast
  from c2_def c3_def c2'c3'disjoint have c2c3disjoint: "c2 \<inter> c3 ={}"
    by blast
  from c1c2disjoint c1c3disjoint c2c3disjoint have colordisjoint:
    "\<forall>c\<in>{c1, c2, c3}. \<forall>c'\<in>{c1, c2, c3}. c \<noteq> c' \<longrightarrow> c \<inter> c' = {}"
    by blast

  have c1_iscolor:"\<And>v. \<And>v'. v\<in>c1 \<Longrightarrow> v'\<in>c1 \<Longrightarrow> {v, v'} \<notin> E"
  proof -
    fix v v'
    assume asms2: "v\<in> c1" "v'\<in> c1"
    from this c1_def have "(v,0)\<in> c1' \<and> (v',0)\<in> c1'"
      by blast
    from this c1'_color have "{(v,0),(v',0)}\<notin>E'"
      by blast
    from this asms(2) E'_def_3 show "{v,v'}\<notin> E"
      using TC_chrN_edge_in_E_iff
      by blast
  qed

  have c2_iscolor:"\<And>v. \<And>v'. v\<in>c2 \<Longrightarrow> v'\<in>c2 \<Longrightarrow> {v, v'} \<notin> E"
  proof -
    fix v v'
    assume asms2: "v\<in> c2" "v'\<in> c2"
    from this c2_def have "(v,0)\<in> c2' \<and> (v',0)\<in> c2'"
      by blast
    from this c2'_color have "{(v,0),(v',0)}\<notin>E'"
      by blast
    from this asms(2) E'_def_3 show "{v,v'}\<notin> E"
      using TC_chrN_edge_in_E_iff
      by blast
  qed

  have c3_iscolor:"\<And>v. \<And>v'. v\<in>c3 \<Longrightarrow> v'\<in>c3 \<Longrightarrow> {v, v'} \<notin> E"
  proof -
    fix v v'
    assume asms2: "v\<in> c3" "v'\<in> c3"
    from this c3_def have "(v,0)\<in> c3' \<and> (v',0)\<in> c3'"
      by blast
    from this c3'_color have "{(v,0),(v',0)}\<notin>E'"
      by blast
    from this asms(2) E'_def_3 show "{v,v'}\<notin> E"
      using TC_chrN_edge_in_E_iff
      by blast
  qed

  from c1_iscolor c2_iscolor c3_iscolor have is_color:"\<forall>c\<in>{c1, c2, c3}. \<forall>v\<in>c. \<forall>v'\<in>c. {v, v'} \<notin> E"
    by blast


  from asms(2) color_complete colordisjoint is_color have "is_colorable E {c1, c2, c3}"
    unfolding is_colorable_def
    by blast

  from this colorNoteq have "is_k_colorable E 3 {c1,c2,c3}"
    unfolding is_k_colorable_def
    by simp

  then show "E \<in> three_colorability"
    unfolding three_colorability_def
    by blast
qed




lemma chroNToThreeCol_notugraph:"\<And>E. \<not>ugraph E \<Longrightarrow> TC_chrN E \<in> chromaticNumber \<Longrightarrow> E \<in> three_colorability"
proof -
  fix E :: "nat set set"
  assume asms:"TC_chrN E \<in> chromaticNumber" "\<not> ugraph E"
  obtain E' k  where E'_def:"(E',k) =TC_chrN E"
    by (metis surj_pair)
  from this asms have E'_chrN:"(E',k) \<in> chromaticNumber"
    by simp
  from asms E'_def have "k = (0::nat)"
    unfolding TC_chrN_def
    by auto
  from this E'_chrN have "(E',0::nat) \<in> chromaticNumber"
    by auto
  from this have "False"
    unfolding chromaticNumber_def
    by fastforce
  then show "E \<in> three_colorability"
    by simp
qed

lemma chroNToThreeCol:"\<And>E. TC_chrN E \<in> chromaticNumber \<Longrightarrow> E \<in> three_colorability"
proof -
  fix E :: "nat set set"
  assume asms:"TC_chrN E \<in> chromaticNumber"
  show "E \<in> three_colorability"
  proof (cases "ugraph E")
    case True
    then show ?thesis
      using chroNToThreeCol_ugraph asms
      by blast
  next
    case False
    then show ?thesis
      using chroNToThreeCol_notugraph asms
      by blast
  qed
qed


theorem is_reduction_threeC_chrN:
  "is_reduction TC_chrN three_colorability chromaticNumber"
  unfolding is_reduction_def
  apply  safe
  subgoal using threeColToChroN
    by blast
  using chroNToThreeCol
  by blast

end
