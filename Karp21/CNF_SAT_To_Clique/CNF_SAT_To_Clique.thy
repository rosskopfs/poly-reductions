section\<open>CNF Sat to Clique\<close>

theory CNF_SAT_To_Clique
  imports Main "../TSAT_To_SC/TSAT_To_SC"
begin

subsection \<open>Preliminaries\<close>

definition
  "ugraph_nodes E V \<equiv> ugraph E \<and>  \<Union> E \<subseteq> V \<and> finite V"

definition cnf_sat where
  "cnf_sat \<equiv> {F. sat F \<and> (\<forall>c \<in> set F. finite c)}"

definition
  "is_clique E C \<equiv> \<forall>u \<in> C. \<forall>v \<in> C. v=u \<or> {u, v} \<in> E"

definition
  "clique \<equiv> {(E, V , k). \<exists>C. ugraph_nodes E V \<and> C \<subseteq> V \<and> card C \<ge> k \<and> is_clique E C}"

definition
  "cnf_sat_to_clique F \<equiv> (if finite (\<Union> (set F)) then (
    {{(l1, i), (l2, j)} | l1 l2 i j. i < length F \<and> j < length F \<and> i\<noteq> j \<and> \<not> conflict l1 l2 \<and>
         l1 \<in> F ! i \<and> l2 \<in> F ! j},
    {(l1, i) | l1 i. i < length F \<and>   l1 \<in> F ! i},
    length F) else ({}, {}, 1))"

subsection \<open>F \<in> cnf_sat \<Longrightarrow> cnf_sat_to_clique F \<in> clique\<close>

definition get_some_true where
  "get_some_true F \<sigma> i \<equiv> SOME l. lift \<sigma> l \<and> l \<in> F ! i"


lemma models_smaller: "models \<sigma> (a#F) \<Longrightarrow> models \<sigma> F"
  by(auto simp add: models_def)


context
  fixes F E V k assumes triple: "cnf_sat_to_clique F = (E, V, k)"
  fixes \<sigma> assumes sigma_def: "models \<sigma> F"
  fixes C assumes C_def: "C \<equiv> {(get_some_true F \<sigma> i, i) |i. i < length F}"
  assumes F_wf: "F \<in> cnf_sat"
begin

lemma fin_1:"finite (\<Union> (set F))"
  using \<open>F \<in> cnf_sat\<close>
  unfolding cnf_sat_def
  by (auto 4 3 intro: card_ge_0_finite)


lemma V_def: "V = {(l1, i) | l1 i. i < length F \<and>   l1 \<in> F ! i}"
  using cnf_sat_to_clique_def fin_1 triple
  by (metis (mono_tags, lifting) fst_conv old.prod.exhaust snd_conv)


lemma E_def: "E = {{(l1, i), (l2, j)} | l1 l2 i j. i < length F
         \<and> j < length F \<and> i\<noteq> j \<and> \<not> conflict l1 l2 \<and>
         l1 \<in> F ! i \<and> l2 \<in> F ! j} " using cnf_sat_to_clique_def triple fin_1
  by (metis (mono_tags, lifting) fst_eqD)


text\<open>Similar to the proof in TSAT_To_SC\<close>
lemma cnf_sat_to_clique_ugraph: "ugraph E"
proof -
  let ?S = "((\<Union> (set F)) \<times> {0..<length F}) \<times> ((\<Union> (set F)) \<times> {0..<length F})"
  show ?thesis
    using triple fin_1
    unfolding cnf_sat_to_clique_def is_clique_def ugraph_def
    by (fastforce intro: finite_surj[where A = "?S"])
qed


lemma edges_between_nodes:
  assumes "X \<in> E"
  shows " X \<subseteq> V"
  using assms triple E_def V_def
  by(auto)


lemma finite_V:
  shows "finite V"
proof -
  let ?S = "((\<Union> (set F)) \<times> {0..<length F})"
  show ?thesis
    using triple fin_1
    unfolding cnf_sat_to_clique_def is_clique_def ugraph_def
    by (fastforce intro: finite_surj[where A = "?S"])
qed


lemma cnf_sat_to_clique_ugraph_nodes:
  shows "ugraph_nodes E V"
  apply(auto simp add: cnf_sat_to_clique_ugraph ugraph_nodes_def F_wf finite_V)
  using edges_between_nodes F_wf
  by blast


lemma get_some_true_aux:
  assumes "i < length F"
  shows "(\<sigma>\<up>) (get_some_true F \<sigma> i) \<and> (get_some_true F \<sigma> i) \<in> F ! i"
  using assms sigma_def
  unfolding models_def get_some_true_def
  by - (rule someI_ex, auto)


lemmas
  get_some_true_sat = get_some_true_aux[THEN conjunct1]
  and
  get_some_true_index = get_some_true_aux[THEN conjunct2]


lemma get_some_true_yields_clique:
  assumes "u\<in>C" "v\<in>C"
  shows "{u, v} \<in> E \<or> u = v"
  using assms triple E_def V_def C_def conflict_models_ccontr
    get_some_true_index get_some_true_sat by blast+


lemma is_clique:
  shows "is_clique E  C"
  unfolding is_clique_def
  using get_some_true_yields_clique F_wf sigma_def
  by(fastforce)


lemma cnf_sat_has_pos: "F \<noteq> []  \<Longrightarrow> \<exists>p. lift \<sigma> p"
  by(auto simp add: models_def lift_def cnf_sat_def split: lit.split)


lemma all_clauses_have_pos: "\<forall>i < (length F). \<exists>p \<in> F!i. lift \<sigma> p"
  using F_wf sigma_def
  by(auto simp add: models_def lift_def cnf_sat_def split: lit.split)


lemma card_clique:
  shows "card C \<ge> length F"
  unfolding F_wf C_def setcompr_eq_image
  by (subst card_image) (auto intro: inj_onI)


lemma in_clique_implies_in_nodes:
  assumes "v \<in> C"
  shows "v \<in> V"
  using assms V_def C_def triple assms get_some_true_index
  by force

lemma clique_in_graph:
  shows "C\<subseteq> V"
  using in_clique_implies_in_nodes
  by blast


lemma in_clique: "cnf_sat_to_clique F \<in> clique"
proof -
  have is_c: "is_clique E C"
    using is_clique
    by auto
  then have card_C_length: "card C \<ge> (length F)"
    using card_clique
    by auto
  then have card_C: "card C \<ge> k"
    using cnf_sat_to_clique_def triple
    by (simp add: cnf_sat_to_clique_def fin_1)
  have clique_contained: "C \<subseteq> V"
    using clique_in_graph
    by blast
  have ug: "ugraph_nodes E V"
    using  cnf_sat_to_clique_ugraph_nodes
    by(auto)
  then have "\<exists> C'. ugraph_nodes (fst (cnf_sat_to_clique F)) (fst (snd( cnf_sat_to_clique F)))
      \<and> C' \<subseteq> fst(snd (cnf_sat_to_clique F)) \<and> card C' \<ge> (snd (snd(cnf_sat_to_clique F)))
      \<and> is_clique (fst (cnf_sat_to_clique F)) C'"
    using card_C is_c clique_contained ug triple
    by(auto)
  then have "cnf_sat_to_clique F \<in>
    {(E, V, k). \<exists>C. ugraph_nodes E V \<and> C \<subseteq> V \<and> card C \<ge> k \<and> is_clique E C}"
    by (simp add: case_prod_beta')
  then show ?thesis
    using clique_def
    by(auto simp add: clique_def)
qed

end

subsection\<open>cnf_sat_to_clique F \<in> clique \<Longrightarrow> F \<in> cnf_sat\<close>

context
  fixes F E V k assumes triple: "cnf_sat_to_clique F = (E, V, k)"
  assumes in_clique: "(E, V, k) \<in> clique"
begin


lemma not_finite_implies_not_finite:
  assumes "\<not> (\<forall>c \<in> set F. finite c)"
  shows "V = {}"
  using assms triple cnf_sat_to_clique_def
  by (metis (no_types, lifting) Pair_inject Union_upper finite_subset)

lemma else_not_in_clique: "({}, {}, 1) \<notin> clique"
  by(auto simp add: clique_def)

lemma aux_for_finite_F:
  assumes "X \<in> set F"
  shows "finite X"
  using assms else_not_in_clique in_clique triple
  unfolding cnf_sat_to_clique_def
  by (auto split: if_split_asm) (meson Sup_upper finite_subset)


lemma aux1: "finite (\<Union> (set F)) \<Longrightarrow>
  E = {{(l1, i), (l2, j)} |l1 l2 i j. i < length F \<and> j < length F
    \<and> i \<noteq> j \<and> \<not> conflict l1 l2 \<and> l1 \<in> F ! i \<and> l2 \<in> F ! j}"
  using triple
  by(auto simp add: cnf_sat_to_clique_def)


lemma finite_F_1:
  assumes "E\<noteq> {} \<or> V \<noteq> {}"
  shows "finite (\<Union> (set F))"
  using cnf_sat_to_clique_def triple
  apply(auto simp add: cnf_sat_to_clique_def)
  by (metis (no_types, lifting) else_not_in_clique local.in_clique)


lemma E_def_C:
  assumes "E \<noteq> {}"
  shows "E= {{(l1, i), (l2, j)} | l1 l2 i j. i < length F \<and> j < length F
        \<and> i\<noteq> j \<and> \<not> conflict l1 l2 \<and> l1 \<in> F ! i \<and> l2 \<in> F ! j}"
  using triple finite_F_1 aux1 assms
  by auto

lemma finite_F:
  shows  "finite (\<Union> (set F))"
  using else_not_in_clique cnf_sat_to_clique_def E_def_C triple finite_F_1 in_clique
  by (simp add: aux_for_finite_F)

lemma no_edges_between_clause:
  assumes "{(l1, i), (l2, i)} \<in> E"
  shows False
proof -
  have "E \<noteq> {}"
    using assms
    by auto
  then have "i \<noteq> i"
    using assms triple E_def_C by simp (metis (lifting) Pair_inject doubleton_eq_iff)
  then show ?thesis
    by auto
qed

lemma conflict_commutative: "conflict l1 l2 = conflict l2 l1"
  by(auto simp add: conflict_def)

lemma edge_conflict_aux:
  assumes "{(l1, i), (l2, j)} \<in>E"
  shows "\<not> conflict l1 l2"
proof (rule ccontr)
  assume "\<not> \<not> conflict l1 l2"
  then have "conflict l1 l2 \<and> conflict l2 l1"
    by (auto simp add: conflict_commutative)
  have "\<not>conflict l1 l2 \<or> \<not> conflict l2 l1"
    using assms triple E_def_C
    apply(auto)
    by (smt Pair_inject doubleton_eq_iff empty_iff mem_Collect_eq)
  then have "\<not> conflict l1 l2"
    using conflict_commutative
    by(auto)
  then show False
    using assms \<open>\<not> \<not> conflict l1 l2\<close>
    by auto
qed

lemma aux5: "v\<in> C \<and> u \<in> C \<and> card C \<le> 1 \<and> finite C\<Longrightarrow> u = v"
  by(auto simp add: card_le_Suc0_iff_eq)

lemma no_conflicts_in_edges_empty_E:
  assumes "is_clique E C" "(l1, i) \<in> C" "(l2, j) \<in> C" "conflict l1 l2" "E = {}" "finite C"
  shows "False"
proof -
  have "card C \<le> 1"
    using assms is_clique_def
    apply(auto)
    by (metis assms(1, 6) card_le_Suc0_iff_eq emptyE is_clique_def)
  then have "(l1, i) = (l2, j)"
    using \<open>(l1, i) \<in> C\<close> \<open>(l2, j) \<in> C\<close> aux5  assms
    by fastforce
  then have "\<not> conflict l1 l2"
    by auto
  then show ?thesis
    using assms
    by(auto)
qed

lemma no_conflicts_in_edges:
  assumes "is_clique E C" "(l1, i) \<in> C" "(l2, j) \<in> C" "conflict l1 l2" "E \<noteq> {}"
  shows "False"
proof -
  have in_E: "{(l1, i), (l2, j)} \<in> E"
    using assms is_clique_def
    by (metis Pair_inject conflict_same)
  then have "\<not> conflict l1 l2"
    using E_def_C edge_conflict_aux
    by auto
  then show ?thesis
    using assms
    by(auto)
qed

lemma f_sat:
  shows "sat F"
proof -
  from triple in_clique have "length F = k"
    unfolding cnf_sat_to_clique_def else_not_in_clique
    by (metis (no_types, lifting) else_not_in_clique old.prod.inject)
  have fin_2: "finite V"
    using in_clique clique_def ugraph_nodes_def
    apply(auto)
    by fastforce
  from in_clique obtain C where C:
    "ugraph_nodes E V" "C \<subseteq> V" "card C \<ge> k" "is_clique E C"
    using cnf_sat_to_clique_def \<open>cnf_sat_to_clique _ = _\<close> in_clique clique_def
    by (smt case_prodD mem_Collect_eq)
  define \<sigma> where "\<sigma> \<equiv> \<lambda>x. (\<exists>i. (Pos x, i) \<in> C)"
  have V_inj: "l = l'" if "(l, i) \<in> C" "(l', i) \<in> C" for l l' i
  proof (rule ccontr)
    from that C(2) have "i < length F"
      using \<open>cnf_sat_to_clique _ = _\<close>
      unfolding cnf_sat_to_clique_def
      by(auto simp add: finite_F)
    from that C(2) have "l \<in> F ! i" "l' \<in> F ! i"
      using \<open>cnf_sat_to_clique _ = _\<close>
      unfolding cnf_sat_to_clique_def
      by(auto simp add: finite_F)
    assume "l \<noteq> l'"
    with \<open>l \<in> _\<close> \<open>l' \<in> _\<close> \<open>i < _\<close> have "{(l, i), (l', i)} \<notin> E"
      using \<open>cnf_sat_to_clique _ = _\<close>
      unfolding cnf_sat_to_clique_def
      by (metis (no_types, lifting)no_edges_between_clause)
    with C(4) that \<open>l \<noteq> l'\<close> show False
      unfolding is_clique_def
      by auto
  qed
  have fin_3: "finite C"
    using C fin_2 finite_subset
    by auto
  have 1: "i < length F \<and> l \<in> F ! i" if "(l, i) \<in> C" for l i
    using that C(2) using \<open>cnf_sat_to_clique _ = _\<close>
    unfolding cnf_sat_to_clique_def by (auto simp add: finite_F)
  then have C_sub: "C \<subseteq> (\<lambda>i. (SOME l. (l, i) \<in> C, i)) ` {0..<length F}"
    by (auto 4 3 intro: someI V_inj)
  have 2: "\<exists>l. (l, i) \<in> C" if "i < length F" for i
  proof (rule ccontr)
    assume "\<nexists>l. (l, i) \<in> C"
    with that C_sub have "C \<subset> (\<lambda>i. (SOME l. (l, i) \<in> C, i)) ` {0..<length F}"
      by fastforce
    then have "card C < length F"
      apply -
      apply (drule psubset_card_mono[rotated])
      using card_image_le[of "{0..<length F}" "\<lambda>i. (SOME l. (l, i) \<in> C, i)"]
      by auto
    with \<open>card C \<ge> _\<close> \<open>length F = _\<close> show False
      by simp
  qed
  have no_conflict: False if "(l, i) \<in> C" "(l', j) \<in> C" "conflict l l'" for l l' i j
    using triple that no_conflicts_in_edges C finite_F cnf_sat_to_clique_def E_def_C fin_3
    apply(auto simp add: finite_F no_conflicts_in_edges no_conflicts_in_edges_empty_E)
    using no_conflicts_in_edges_empty_E
    by smt
  have "\<exists>l\<in>cls. (\<sigma>\<up>) l" if "cls \<in> set F" for cls
  proof -
    from that obtain i where "F ! i = cls" "i < length F"
      by (meson in_set_conv_nth)
    then obtain l where "(l, i) \<in> C"
      by (blast dest: 2)
    then have "(\<sigma>\<up>) l"
      unfolding \<sigma>_def lift_def
      by (cases l) (auto simp: conflict_def dest: no_conflict)
    moreover from \<open>_ \<in> C\<close> have "l \<in> cls"
      using \<open>F ! i = _\<close>
      by (auto dest: 1)
    ultimately show ?thesis
      by auto
  qed
  then have "\<sigma> \<Turnstile> F"
    unfolding models_def
    by auto
  then show ?thesis
    by(auto simp add: sat_def)
qed

end


subsection\<open> Main theorem \<close>

(*Just some help for Isabelle, since she was not able to figure that out herself*)
lemma cnf_sat_impl_clique: "F \<in> cnf_sat \<Longrightarrow> cnf_sat_to_clique F \<in> clique"
proof -
  assume f_cnf_sat: "F\<in> cnf_sat"
  then obtain \<sigma>  where "\<sigma> \<Turnstile> F"
    unfolding cnf_sat_def sat_def
    by auto
  then have models_sigma: "models \<sigma> F"
    by auto
  obtain E V k where "cnf_sat_to_clique F = (E, V, k)"
    using cnf_sat_to_clique_def prod_cases3
    by blast
  then show ?thesis
    using in_clique f_cnf_sat models_sigma prod_cases3
    by blast
qed

lemma in_clique_implies_in_cnf_sat:
  assumes "cnf_sat_to_clique F \<in> clique"
  shows "F \<in> cnf_sat"
proof - (*found by sledgehammer*)
  have "\<forall>p Ls. cnf_sat_to_clique (Ls::'a lit set list) \<noteq> p \<or> p \<notin> clique \<or> sat Ls"
    by (simp add: f_sat)
  then have "sat F \<and> (\<forall>L. L \<in> set F \<longrightarrow> finite L)"
    by (metis (no_types) assms aux_for_finite_F old.prod.exhaust)
  then show ?thesis
    using cnf_sat_def
    by auto
qed

theorem is_reduction_cnf_sat_to_clique:
  "is_reduction cnf_sat_to_clique cnf_sat clique"
  unfolding is_reduction_def
  using cnf_sat_impl_clique in_clique_implies_in_cnf_sat
  by auto

end
