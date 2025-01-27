theory XC_To_EHS_Poly
  imports
    SAT_To_XC_Poly
    XC_To_EHS
begin

section "Reduction from the exact cover to the exact hitting set is polynomial"

subsection "Definitions"

definition "mop_check_finiteness_and_is_collection \<equiv> \<lambda>(X, S). SPECT [finite X \<and> \<Union> S \<subseteq> X \<mapsto> 1]"
definition "mop_construct_sets \<equiv> \<lambda>(X, S). SPEC (\<lambda>S'. S' = {{s. u \<in> s \<and> s \<in> S} |u. u \<in> X}) (\<lambda>_. 3 * card S * card X)"
(*
3 * card S for iterating the sets, check if u is contained in s and the insertion
1 * card X for iterating the elements
*)

definition "xc_to_ehs_alg \<equiv> \<lambda>(X, S).
  do {
    b \<leftarrow> mop_check_finiteness_and_is_collection (X, S);
    if b
    then do {
      S' \<leftarrow> mop_construct_sets (X, S);
      RETURNT S' }
    else do {
      RETURNT {{}} }}"

definition "xc_to_ehs_space n \<equiv> 1 + n*n"
definition "xc_to_ehs_time n \<equiv> 1 + 3 * n * n"

subsection "Proof"

lemma card_ehs_le:
assumes "finite X" "card X \<le> Y"
shows "card {{s. u \<in> s \<and> s \<in> S} |u. u \<in> X} \<le> Suc (Y * Y)"
proof -
  let ?f = "\<lambda>u. {s. u \<in> s \<and> s \<in> S}"
  have "?f ` X = {{s. u \<in> s \<and> s \<in> S} |u. u \<in> X}"
    by blast
  with assms have "card {{s. u \<in> s \<and> s \<in> S} |u. u \<in> X} \<le> card X"
    using card_image_le[of X ?f]
    by argo
  also have "... \<le> card X * card X"
    by fastforce
  also have "... \<le> Y * Y"
    using assms(2) mult_le_mono
    by blast
  finally show ?thesis
    by auto
qed

lemma xc_to_ehs_size:
"size_ehs (xc_to_ehs xc) \<le> xc_to_ehs_space (size_XC xc)"
by (auto simp add: size_ehs_def xc_to_ehs_def xc_to_ehs_space_def size_XC_def
 max_def card_ehs_le split: prod.splits)

lemma xc_to_ehs_refines:
"xc_to_ehs_alg xc \<le> SPEC (\<lambda>y. y = xc_to_ehs xc) (\<lambda>_. xc_to_ehs_time (size_XC xc))"
unfolding SPEC_def
unfolding xc_to_ehs_alg_def xc_to_ehs_def xc_to_ehs_time_def
mop_check_finiteness_and_is_collection_def mop_construct_sets_def
apply (rule T_specifies_I)
apply (vcg' \<open>-\<close> rules: T_SPEC)
by (auto simp add: one_enat_def size_XC_def card_ehs_le max_def)

theorem xc_to_ehs_is_polyred:
  "ispolyred xc_to_ehs_alg exact_cover exact_hitting_set size_XC size_ehs"
unfolding ispolyred_def
  apply(rule exI[where x=xc_to_ehs])
  apply(rule exI[where x=xc_to_ehs_time])
  apply(rule exI[where x=xc_to_ehs_space])
  apply safe
  subgoal
    using xc_to_ehs_refines
    by blast
  subgoal
    using xc_to_ehs_size
    by blast
  subgoal
    unfolding poly_def xc_to_ehs_time_def
    apply(intro exI[where x=2])
    by auto
  subgoal
    unfolding poly_def xc_to_ehs_space_def
    apply(intro exI[where x=2])
    by auto
  subgoal
    using is_reduction_xc_to_ehs
    by blast
  done

end