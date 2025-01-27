section \<open>Three Sat to Independent Set\<close>
theory THREE_SAT_To_IS
  imports
    IS_Definition
    Reductions
    SAT_Definition
begin

subsection \<open>Three Sat to Independent Set\<close>

fun conflict_lit where
"conflict_lit (Pos l1) (Neg l2) = (l1 = l2)" |
"conflict_lit (Neg l1) (Pos l2) = (l1 = l2)" |
"conflict_lit _ _ = False"

lemma models_lit_ne_models_lit_if_conflict_lit:
  assumes "conflict_lit x y"
  shows "(\<sigma>\<up>) x \<noteq> (\<sigma>\<up>) y"
  using assms by (cases x; cases y) auto

lemma not_conflict_lit_self [iff]: "\<not>(conflict_lit l l)"
  by (cases l) auto

definition
  "sat_is_un_1 F \<equiv> {{(l1, i), (l2, i)} | l1 l2 i. i < length F \<and> l1 \<in> F ! i \<and> l2 \<in> F ! i \<and> l1 \<noteq> l2}"

definition
  "sat_is_un_2 F \<equiv> {{(l1, i), (l2, j)} | l1 l2 i j.
    i < length F \<and> j < length F \<and> l1 \<in> F ! i \<and> l2 \<in> F ! j \<and> conflict_lit l1 l2}"

definition
  "sat_is F \<equiv> if is_n_sat 3 F then (sat_is_un_1 F \<union> sat_is_un_2 F, length F) else ({}, 1)"

lemmas sat_is_unfold = sat_is_def[unfolded sat_is_un_1_def sat_is_un_2_def]

subsection "Proof"

theorem is_reduction_sat_is: "is_reduction sat_is three_sat independent_set"
proof (rule is_reductionI)
  fix F :: "'a lit set list"
  assume "F \<in> three_sat"
  then obtain \<sigma> where "\<sigma> \<Turnstile> F" by auto
  from \<open>F \<in> _\<close> have fin_1: "finite (\<Union> (set F))" by (fastforce intro: card_ge_0_finite)
  let ?m = "length F"
  let ?l = "\<lambda>i. SOME l. (\<sigma>\<up>) l \<and> l \<in> F ! i"
  define V where "V \<equiv> {(?l i, i) | i. i < ?m}"
  have select: "(\<sigma>\<up>) (?l i) \<and> (?l i) \<in> F ! i" if "i < length F" for i
    using \<open>\<sigma> \<Turnstile> F\<close> that unfolding models_def models_clause_def by - (rule someI_ex, auto)
  { fix l i assume "l \<in> F ! i" "i < length F"
    have "is_n_clause 3 (F ! i)" using \<open>F \<in> _\<close> \<open>i < _\<close> by fastforce
    with \<open>l \<in> _\<close> consider l' where "l \<noteq> l'" "l' \<in> F ! i"
      unfolding numeral_3_eq_3 by (force dest: card_eq_SucD)
  } note pair = this
  obtain E k where "sat_is F = (E, k)" by force
  let ?S = "((\<Union> (set F)) \<times> {0..<length F}) \<times> ((\<Union> (set F)) \<times> {0..<length F})"
  from \<open>F \<in> _\<close> have wf: "is_n_sat 3 F" by auto
  with \<open>sat_is F = _\<close> have "length F = k" unfolding sat_is_def using \<open>F \<in> three_sat\<close> by auto
  have "card V = length F"
    unfolding V_def setcompr_eq_image by (subst card_image) (auto intro: inj_onI)
  moreover have "is_independent_set E V"
    using \<open>sat_is F = (E, k)\<close> wf models_lit_ne_models_lit_if_conflict_lit select
    unfolding sat_is_unfold V_def
    by (intro is_independent_setI) (auto simp: doubleton_eq_iff; blast)
  moreover have "ugraph E"
    using \<open>sat_is F = (E, k)\<close> wf using fin_1 unfolding sat_is_unfold
    by (intro ugraphI) (fastforce intro: finite_surj[where A = "?S"] simp: card_insert_if)+
  moreover have "V \<subseteq> \<Union> E"
    using \<open>sat_is F = (E, k)\<close> wf unfolding V_def sat_is_unfold
    apply simp
    apply (elim conjE)
    apply (drule sym)
    apply simp
    apply (rule subsetI)
    apply (rule UnI1)
    apply clarsimp
    apply (frule select)
    by (blast intro: pair)
  ultimately show "sat_is F \<in> independent_set" by (auto simp: \<open>sat_is _ = _\<close> \<open>length F = _\<close>)
next
  fix F :: "'a lit set list"
  assume "sat_is F \<in> independent_set"
  obtain E k where "sat_is F = (E, k)" by force
  show "F \<in> three_sat"
  proof (cases "is_n_sat 3 F")
    case wf: True
    with \<open>sat_is F = _\<close> have "length F = k" unfolding sat_is_def by simp
    from \<open>sat_is F \<in> _\<close> obtain V where V: "ugraph E" "V \<subseteq> \<Union> E" "card V \<ge> k" "is_independent_set E V"
      unfolding \<open>sat_is _ = _\<close> by auto
    define \<sigma> where "\<sigma> \<equiv> \<lambda>x. (\<exists>i. (Pos x, i) \<in> V)"
    have V_inj: "l = l'" if "(l, i) \<in> V" "(l', i) \<in> V" for l l' i
    proof (rule ccontr)
      from that V(2) have "i < length F"
        using \<open>sat_is _ = _\<close> wf unfolding sat_is_unfold by auto
      from that V(2) have "l \<in> F ! i" "l' \<in> F ! i"
        using \<open>sat_is _ = _\<close> wf unfolding sat_is_unfold by fastforce+
      assume "l \<noteq> l'"
      with \<open>l \<in> _\<close> \<open>l' \<in> _\<close> \<open>i < _\<close> have "{(l, i), (l', i)} \<in> E"
        using \<open>sat_is _ = _\<close> wf unfolding sat_is_unfold by auto
      with V(4) that show False by auto
    qed
    have 1: "i < length F \<and> l \<in> F ! i" if "(l, i) \<in> V" for l i
      using that V(2) using \<open>sat_is _ = _\<close> wf unfolding sat_is_unfold by auto
    then have V_sub: "V \<subseteq> (\<lambda>i. (SOME l. (l, i) \<in> V, i)) ` {0..<length F}"
      by (auto 4 3 intro: someI V_inj)
    have 2: "\<exists>l. (l, i) \<in> V" if "i < length F" for i
    proof (rule ccontr)
      assume "\<nexists>l. (l, i) \<in> V"
      with that V_sub have "V \<subset> (\<lambda>i. (SOME l. (l, i) \<in> V, i)) ` {0..<length F}"
        by fastforce
      then have "card V < length F"
        apply -
        apply (drule psubset_card_mono[rotated])
        using card_image_le[of "{0..<length F}" "\<lambda>i. (SOME l. (l, i) \<in> V, i)"]
        by auto
      with \<open>card V \<ge> _\<close> \<open>length F = _\<close> show False by simp
    qed
    have no_conflict: False if "(l, i) \<in> V" "(l', j) \<in> V" "conflict_lit l l'" for l l' i j
      using \<open>sat_is F = (E, k)\<close> that unfolding sat_is_unfold
      by (simp add: wf) (smt 1 UnCI V(4) is_independent_set_def mem_Collect_eq prod.sel(1))
    have "\<exists>l\<in>cls. (\<sigma>\<up>) l" if "cls \<in> set F" for cls
    proof -
      from that obtain i where "F ! i = cls" "i < length F"
        by (meson in_set_conv_nth)
      then obtain l where "(l, i) \<in> V"
        by (blast dest: 2)
      then have "(\<sigma>\<up>) l" unfolding \<sigma>_def using no_conflict by (cases l) fastforce+
      moreover from \<open>_ \<in> V\<close> have "l \<in> cls" using \<open>F ! i = _\<close> by (auto dest: 1)
      ultimately show ?thesis by auto
    qed
    then have "\<sigma> \<Turnstile> F" by fastforce
    with wf show "F \<in> three_sat" by auto
  next
    case False
    with \<open>sat_is F \<in> _\<close> show "F \<in> three_sat" unfolding sat_is_def by auto
  qed
qed

end