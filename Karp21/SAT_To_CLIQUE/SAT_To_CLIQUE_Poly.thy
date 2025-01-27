theory SAT_To_CLIQUE_Poly
  imports
    SAT_To_CLIQUE
    THREE_SAT_To_SC_Poly
begin

subsection\<open>The reduction from \<open>Sat\<close> to \<open>Clique\<close> is polynomial\<close>

subsubsection\<open>Definitions\<close>

definition "max_size_clauses xs = card (\<Union> (set xs))"

definition "add_edges_cstc F S =
  SPECT [ S \<union> {{(l1, i), (l2, j)} | l1 l2 i j.
      i < length F \<and> j < length F \<and> l1 \<in> F ! i \<and> l2 \<in> F ! j \<and> \<not> conflict_lit l1 l2 \<and> i \<noteq> j}
       \<mapsto> max_size_clauses F * max_size_clauses F * length F * length F]"

definition "add_nodes_cstc F V =
  SPECT [ V \<union>  {(l1, i) | l1 i. i < length F \<and>   l1 \<in> F ! i}
       \<mapsto> max_size_clauses F * length F]"

definition sat_to_clique_alg ::
  "'a lit set list \<Rightarrow> (('a lit \<times> nat) set set \<times> ('a lit \<times> nat) set  \<times> nat) nrest" where
  "sat_to_clique_alg = (\<lambda>F. do {
      b \<leftarrow> SPECT [ finite (\<Union> (set F)) \<mapsto> 1];
      if b then
        do {
          l \<leftarrow> mop_list_length F;
          S \<leftarrow> mop_set_empty_set;
          S \<leftarrow> add_edges_cstc F S;
          V \<leftarrow> mop_set_empty_set;
          V \<leftarrow> add_nodes_cstc F V;
          RETURNT ( S, V, l)
        }
      else RETURNT ( {}, {}, 1 )
    })"


definition "number_clauses_sat xs = length xs"
definition size_SAT where "size_SAT xs = number_clauses_sat xs * max_size_clauses xs"
definition "sat_to_clique_time n = 4 + n * n  + n"
  (*where n is number of clauses times maximum length of the clauses*)
definition "size_CLIQUE = (\<lambda>(E,V,k). card E + card V)"
definition "sat_to_clique_space n  = n * n + n"


subsubsection\<open>Auxiliary proofs\<close>

lemma brr2:
  shows "{{f l1, g l2} |l1 l2.  h l1 l2 \<and> l1 \<in> X \<and> l2 \<in> Y}
  \<subseteq> (\<Union>x \<in> X. \<Union>y \<in> Y. {{f x, g y}})"
  using brr by auto

lemma upperbounding_card_m:
  "\<forall>x\<in>X. card x \<le> m \<and> finite x \<Longrightarrow> x\<in>X \<Longrightarrow> y\<in>X \<Longrightarrow>
        card {{f l1, g l2} |l1 l2. h l1 l2 \<and> l1 \<in> x \<and> l2 \<in> y } \<le> m*m"
  apply(rule order.trans)
   apply(rule card_mono) defer
    apply(rule brr2)
   apply(rule order.trans) apply(rule card_Un)
  subgoal by auto
   apply(rule order.trans) apply(rule sum_image_le)
  subgoal using aaa by auto
    apply simp  apply(rule order.trans)
    apply(rule sum_mono[where g="\<lambda>_. m"]) apply simp
    apply(rule order.trans) apply(rule card_Un)
  subgoal apply (rule finite_imageI) using aaa by auto
    apply(rule order.trans) apply(rule sum_image_le)
  subgoal by auto
     apply simp apply simp apply(simp)
  apply(rule finite_Union)
   apply (rule finite_imageI) by auto

lemma card_x_smaller_card_union:
  assumes "x \<in> set xs" "finite (\<Union> (set xs))"
  shows "card x \<le> card (\<Union> (set xs))"
proof -
  have "x \<subseteq> \<Union> (set xs)"
    using \<open>x\<in>set xs\<close>  by auto
  then show ?thesis
    using assms by (simp add: card_mono)
qed

lemma upperbounding_card_union: assumes "\<forall>x\<in>X. card x \<le> card (\<Union> X) \<and> finite x" "x\<in>X" "y\<in>X"
  shows "card {{f l1, g l2} |l1 l2. h l1 l2 \<and> l1 \<in> x \<and> l2 \<in> y } \<le> card (\<Union> X) * card (\<Union> X)"
  using assms by(auto simp add: upperbounding_card_m )

lemma upperbounding_card_union2:
  assumes "finite (\<Union> X)" "x\<in>X" "y\<in>X"
  shows "card {{f l1, g l2} |l1 l2. \<not> h l1 l2 \<and> l1 \<in> x \<and> l2 \<in> y } \<le> card (\<Union> X) * card (\<Union> X)"
proof -
  from assms have 1: "\<forall>x\<in>X. finite x"
    apply(auto)
    by (simp add: Sup_upper rev_finite_subset)
  then have 2: "\<forall>x \<in>X. card x \<le> card (\<Union> X)"
    using card_x_smaller_card_union assms
    by (simp add: Sup_upper card_mono)
  from 1 2 assms
  show ?thesis
    by(auto simp add: upperbounding_card_union)
qed

lemma upperbounding_card_union3:
  assumes "finite (\<Union> (set F))" "i < length F" "j<length F"
  shows "card {{(l1, i), (l2, j)} |l1 l2.  i \<noteq> j \<and> \<not> h l1 l2 \<and> l1 \<in> F!i  \<and> l2 \<in> F!j}
    \<le> card (\<Union> (set F)) * card (\<Union> (set F))"
proof -
  obtain X where "X = F!i"
    by auto
  then have 1: "X \<in> set F"
    using assms
    by(auto)
  obtain Y where "Y = F!j"
    by auto
  then have 2: "Y \<in> set F"
    using assms
    by(auto)
  then have "{{(l1, i), (l2, j)} |l1 l2.  i \<noteq> j \<and> \<not> h l1 l2 \<and> l1 \<in> F!i  \<and> l2 \<in> F!j} =
    {{(l1, i), (l2, j)} |l1 l2.  i \<noteq> j \<and> \<not> h l1 l2 \<and> l1 \<in> X  \<and> l2 \<in> Y}"
    using \<open>X = _\<close> \<open>Y=_\<close>
    by(auto)
  then have 3: "card {{(l1, i), (l2, j)} |l1 l2.  i \<noteq> j \<and> \<not> h l1 l2 \<and> l1 \<in> F!i  \<and> l2 \<in> F!j} =
    card {{(l1, i), (l2, j)} |l1 l2.  i \<noteq> j \<and> \<not> h l1 l2 \<and> l1 \<in> X  \<and> l2 \<in> Y}"
    by(auto)
  have 4: "{{(l1, i), (l2, j)} |l1 l2.  i \<noteq> j \<and> \<not> h l1 l2 \<and> l1 \<in> X  \<and> l2 \<in> Y}
    \<subseteq> {{(l1, i), (l2, j)} |l1 l2. \<not> h l1 l2 \<and> l1 \<in> X  \<and> l2 \<in> Y}"
    by blast
  let ?S = "((\<Union> (set F)) \<times> {0..<length F})\<times> ((\<Union> (set F)) \<times> {0..<length F})"
  have "finite {{(l1, i), (l2, j)} |l1 l2. \<not> h l1 l2 \<and> l1 \<in> F!i  \<and> l2 \<in> F!j}"
    using assms
    by (fastforce intro: finite_surj[where A = "?S"])
  then have "finite {{(l1, i), (l2, j)} |l1 l2. \<not> h l1 l2 \<and> l1 \<in> X  \<and> l2 \<in> Y}"
    using \<open>X = _\<close> \<open>Y=_\<close>
    by(auto)
  then have 5: "card {{(l1, i), (l2, j)} |l1 l2.  i \<noteq> j \<and> \<not> h l1 l2 \<and> l1 \<in> X  \<and> l2 \<in> Y}
      \<le> card {{(l1, i), (l2, j)} |l1 l2. \<not> h l1 l2 \<and> l1 \<in> X  \<and> l2 \<in> Y}"
    by (simp add: "4" card_mono)
  have "card {{(l1, i), (l2, j)} |l1 l2. \<not> h l1 l2 \<and> l1 \<in> X  \<and> l2 \<in> Y}
      \<le> card (\<Union> (set F)) * card (\<Union> (set F))" using 1 2 4 assms
    by(auto simp add:upperbounding_card_union2)
  then show ?thesis
    using 1 2 3 4 5
    by(auto)
qed

lemma card_clauses_samller: "x \<in> set xs \<and> finite (\<Union> (set xs)) \<Longrightarrow> card x \<le> max_size_clauses xs"
  by(auto simp add: max_size_clauses_def card_x_smaller_card_union)

lemma card_V:
  assumes "finite (\<Union> (set p))"
  shows "card {(l1, i). i < length p \<and> l1 \<in> p ! i} \<le> length p * card (\<Union> (set p))"
proof -
  let ?S = "((\<Union> (set p)) \<times> {0..<length p})"
  let ?V = " {(l1, i). i < length p \<and> l1 \<in> p ! i}"
  have 1: "card ?S \<le> (card (\<Union> (set p))) * length p"
    by (simp add: card_cartesian_product)
  moreover have "?V \<subseteq> ?S"
    by force
  ultimately show ?thesis
    by (metis (no_types, lifting) assms card_mono dual_order.trans finite_SigmaI
        finite_atLeastLessThan mult.commute)
qed

lemma card_E2:
  assumes "finite (\<Union> (set F))"
  shows "card {{(l1, i), (l2, j)} |l1 l2 i j. i < length F \<and> j < length F
      \<and> i \<noteq> j \<and> \<not> conflict_lit l1 l2 \<and> l1 \<in> F ! i \<and> l2 \<in> F ! j}
            \<le> length F * card (\<Union> (set F)) * length F * card (\<Union> (set F))"
  apply(subst paf2)
  apply(subst paf)
  apply(rule order.trans) apply(rule card_Un) apply simp
  apply(rule order.trans)
   apply(rule sum_image_le) apply simp apply simp
  apply(rule order.trans)
   apply(rule sum_mono[where g="\<lambda>_. card (\<Union> (set F))* card (\<Union> (set F))  * length F"])
  subgoal apply simp
    apply(rule order.trans) apply(rule card_Un) apply simp
    apply(rule order.trans)
     apply(rule sum_image_le) apply simp apply simp
    apply(rule order.trans)
     apply(rule sum_mono[where g="\<lambda>_. card (\<Union> (set F)) * card (\<Union> (set F))"])
    subgoal
      apply simp using assms upperbounding_card_union3 by(auto)
    apply simp done
  subgoal apply simp done
  done

lemma card_E3:
  assumes "finite (\<Union> (set F))"
  shows "card {{(l1, i), (l2, j)} |l1 l2 i j. i < length F \<and> j < length F
    \<and> i \<noteq> j \<and> \<not> conflict_lit l1 l2 \<and> l1 \<in> F ! i \<and> l2 \<in> F ! j}
            \<le> length F * card (\<Union> (set F)) * (length F * card (\<Union> (set F)))"
proof -
  have "card {{(l1, i), (l2, j)} |l1 l2 i j. i < length F \<and> j < length F
    \<and> i \<noteq> j \<and> \<not> conflict_lit l1 l2 \<and> l1 \<in> F ! i \<and> l2 \<in> F ! j}
    \<le> length F * card (\<Union> (set F)) * length F * card (\<Union> (set F))" using assms by(rule card_E2)
  then have "card {{(l1, i), (l2, j)} |l1 l2 i j. i < length F \<and> j < length F
    \<and> i \<noteq> j \<and> \<not> conflict_lit l1 l2 \<and> l1 \<in> F ! i \<and> l2 \<in> F ! j}
    \<le> length F * card (\<Union> (set F)) * (length F * card (\<Union> (set F)))"  by(auto)
  then show ?thesis .
qed


subsubsection\<open>Main proofs\<close>

lemma sat_to_clique_size: "size_CLIQUE (sat_to_clique p)
  \<le> sat_to_clique_space (size_SAT p)"
  by (auto intro: add_mono
      simp: size_CLIQUE_def sat_to_clique_def sat_to_clique_space_def
        size_SAT_def number_clauses_sat_def max_size_clauses_def card_E3 card_V)

lemma sat_to_clique_refines:
  "sat_to_clique_alg F \<le>
   SPEC (\<lambda>y. y = sat_to_clique F) (\<lambda>_. sat_to_clique_time (size_SAT F))"
  unfolding SPEC_def sat_to_clique_alg_def sat_to_clique_def
    mop_list_length_def mop_set_empty_set_def add_edges_cstc_def
    add_nodes_cstc_def
  apply(rule T_specifies_I)
  apply(vcg' \<open>-\<close> rules: T_SPEC )
  by(auto simp: sat_to_clique_time_def number_clauses_sat_def
      max_size_clauses_def one_enat_def size_SAT_def)

theorem sat_to_clique_ispolyred:
  "ispolyred sat_to_clique_alg fin_sat clique size_SAT size_CLIQUE"
  unfolding ispolyred_def
  apply(rule exI[where x=sat_to_clique])
  apply(rule exI[where x=sat_to_clique_time])
  apply(rule exI[where x=sat_to_clique_space])
  apply(safe)
  subgoal using sat_to_clique_refines by blast
  subgoal using sat_to_clique_size by blast
  subgoal unfolding poly_def sat_to_clique_time_def apply(rule exI[where x=2]) by auto
  subgoal unfolding poly_def sat_to_clique_space_def apply(rule exI[where x=2]) by auto
  subgoal using is_reduction_sat_to_clique .
  done

end
