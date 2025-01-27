theory XC_To_SS_Poly
  imports
    XC_To_SS
    SAT_To_XC_Poly
begin

section "the reduction from the exact cover to subset sum is polynomial"

subsection "definitions"

definition "mop_check_finite_collection \<equiv> (\<lambda>(X, S). SPECT [infinite X \<or> (\<not> \<Union>S \<subseteq> X) \<mapsto> 1])"
definition "mop_constr_bij_mapping \<equiv> (\<lambda>(X, _). SPEC (\<lambda>f. f = map_to_nat X) (\<lambda>_. 3 * card X + 1))"
definition "mop_constr_base \<equiv> (\<lambda>(_, S). SPEC (\<lambda>p. p = max 2 (card S + 1)) (\<lambda>_. card S + 3))"
definition "mop_constr_weight \<equiv> (\<lambda>p f. SPEC (\<lambda>w. w = (\<lambda>A.  (weight p (f ` A)))) (\<lambda>_. 1))"
definition "mop_constr_B \<equiv> (\<lambda>p f X. SPEC (\<lambda>B.  B =  (weight p (f ` X))) (\<lambda>_. 3 * card X + 1))"
(*bij_mapping:
  3 for obtaining the element, constructing the mapping and updating the construction
  1 for the bijection check
  base:
  1 for obtaining cardinality
  3 for constant 2, incrementation and maximum comparison
  weight:
  1 for function construction
  B:
  3 for obtainting the element, power arithmetics and addition arithmetics
  1 for the function construction
*)

definition "xc_to_ss_alg \<equiv> (\<lambda>(X, S).
  do {
    b \<leftarrow> mop_check_finite_collection (X, S);
    if b
    then do {
        RETURNT ({},  card, 1)
    }
    else do {
        f \<leftarrow> mop_constr_bij_mapping (X, S);
        p \<leftarrow> mop_constr_base (X, S);
        w \<leftarrow> mop_constr_weight p f;
        B \<leftarrow> mop_constr_B p f X;
        RETURNT (S, w, B)
    }
  }
)"

definition "xc_to_ss_space n = 1 + n + 1 + n + 1"

definition "xc_to_ss_time n = 1 + (3 * n + 1) + (n + 3) + 1 + (3 * n + 1)"

subsection "proofs"

lemma xc_to_ss_size:
"size_SS (xc_to_ss (X, S)) \<le> xc_to_ss_space (size_XC (X, S))"
apply (simp add: size_SS_def xc_to_ss_def xc_to_ss_space_def size_XC_def)
by (auto simp add: Let_def)

lemma xc_to_ss_refines:
"xc_to_ss_alg (X, S) \<le> SPEC (\<lambda>y. y = xc_to_ss (X, S)) (\<lambda>_. xc_to_ss_time (size_XC (X, S)))"
unfolding SPEC_def
unfolding xc_to_ss_alg_def xc_to_ss_def mop_check_finite_collection_def
mop_constr_bij_mapping_def mop_constr_base_def mop_constr_weight_def
mop_constr_B_def
apply(rule T_specifies_I)
apply(vcg' \<open>-\<close> rules: T_SPEC )
by (auto simp add:  xc_to_ss_time_def size_XC_def one_enat_def Let_def)

theorem xc_to_ss_ispolyred:
  "ispolyred xc_to_ss_alg exact_cover subset_sum size_XC size_SS"
  unfolding ispolyred_def
  apply(rule exI[where x=xc_to_ss])
  apply(rule exI[where x=xc_to_ss_time])
  apply(rule exI[where x=xc_to_ss_space])
  apply safe
  subgoal
    using xc_to_ss_refines
    by blast
  subgoal
    using xc_to_ss_size
    by blast
  subgoal
    unfolding Polynomial_Growth_Functions.poly_def xc_to_ss_time_def
    apply(intro exI[where x=2])
    by auto
  subgoal
    unfolding Polynomial_Growth_Functions.poly_def xc_to_ss_space_def
    apply(intro exI[where x=2])
    by auto
  subgoal
    using is_reduction_xc_to_ss .
  done

end