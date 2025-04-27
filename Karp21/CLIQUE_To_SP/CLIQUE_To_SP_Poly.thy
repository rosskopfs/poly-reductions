theory CLIQUE_To_SP_Poly
  imports
    CLIQUE_To_SP
    Polynomial_Reductions
    Poly_Library
begin

(* TODO: subset in max E V ** 2? *)
― ‹ ugraph_nodes E V \<equiv> ugraph E \<and> \<Union> E \<subseteq> V \<and> (\<forall>e \<in> E. card e = 2) ›
definition "mop_ugraph_nodes E V = SPECT [ ugraph_nodes E V ↦ 1 ]"
definition "mop_set_image_sp E V = SPECT [ (\<lambda>i. { {i,j} | j. j \<in> V \<and> {i, j} \<notin> E }) ` V ↦ card V * card V * card E ]"

(* TODO: refine foldl *)
definition clique_to_set_packing_poly:
  "clique_to_set_packing_poly ≡ λ(E, V, k).
    do {
      b ← mop_ugraph_nodes E V;
      if b then do {
        S <- mop_set_image_sp E V;
        RETURNT (S, k)
      }
      else RETURNT ({}, 1)
    }"

(* TODO: encode k with floor_log *)
(* yanked from SAT_To_CLIQUE_Poly *)
definition "size_CLIQUE = (\<lambda>(E, V, k). card E + card V)"
definition "size_SP = (\<lambda>(S, k). sum card S)"

definition "clique_to_set_packing_space n ≡ n * (n * n + n)"

definition "clique_to_set_packing_time n ≡ 1 + n * n * n"

lemma ugraph_edge_count:
assumes "ugraph_nodes E V"
shows "card E ≤ card V choose 2"
using assms n_subsets ugraph_nodes_def ugraph_def
proof -
  have "E ⊆ {e. e ⊆ V ∧ card e = 2}"
    using assms by (auto simp: ugraph_nodes_def ugraph_def)
  moreover have "finite {e. e ⊆ V ∧ card e = 2}"
    using assms by (auto simp: ugraph_nodes_def ugraph_def)
  ultimately have "card E ≤ card {e. e ⊆ V ∧ card e = 2}"
    by (simp add: card_mono)
  also have "... ≤ card V choose 2"
    using assms by (simp add: n_subsets ugraph_nodes_def)
  finally show ?thesis .
qed

lemma f:
assumes "ugraph_nodes E V" and "x ∈ ((λi. {{i, j} | j. j ∈ V ∧ {i, j} ∉ E}) ` V)"
shows "x ⊆ ({e. e ⊆ V ∧ card e = 2}) ∪ {{v}| v. v ∈ V}"
using assms mem_Collect_eq singleton_insert_inj_eq' subsetI
  by fastforce

lemma sp_image_elem_size:
assumes "finite V"
shows "card (({e. e ⊆ V ∧ card e = 2}) ∪ {{v}| v. v ∈ V}) ≤ (card V choose 2) + card V"
proof -
  have *: "{{v} | v. v ∈ V} = (λv. {v}) ` V" using Setcompr_eq_image .
  have "card (({e. e ⊆ V ∧ card e = 2}) ∪ {{v}| v. v ∈ V}) ≤ card ({e. e ⊆ V ∧ card e = 2}) + card ({{v}| v. v ∈ V})"
    using card_Un_le by blast
  moreover have "... ≤ (card V choose 2) + card ({{v} | v. v ∈ V})" using assms
    by (simp add: le_refl n_subsets)
  moreover have "... ≤ (card V choose 2) + card V" using card_image_le[OF assms] * by auto
  ultimately show ?thesis by linarith
qed

lemma bruh_moment:
assumes "ugraph_nodes E V" and "x ∈ ((λi. {{i, j} | j. j ∈ V ∧ {i, j} ∉ E}) ` V)"
shows "card x ≤ (card V choose 2) + card V"
proof -
  (* lol *)
  have finite_v: "finite V" using assms ugraph_nodes_def by blast
  from finite_v have finite_left: "finite ({e. e ⊆ V ∧ card e = 2})" by auto
  have finite_r': "finite ((λv. {v}) ` V)" using finite_imageI[OF finite_v] by simp
  then have "finite ({{v}| v. v ∈ V})" using Setcompr_eq_image by metis
  then have finite_term: "finite (({e. e ⊆ V ∧ card e = 2}) ∪ {{v}| v. v ∈ V})" using finite_left by force

  have "x ⊆ ({e. e ⊆ V ∧ card e = 2}) ∪ {{v}| v. v ∈ V}" using assms f by fastforce
  then have "card x ≤ card (({e. e ⊆ V ∧ card e = 2}) ∪ {{v}| v. v ∈ V})"
    using card_mono[OF finite_term] by blast
  then show ?thesis
    using sp_image_elem_size by fastforce
qed

lemma card_verteces:
assumes "ugraph_nodes E V"
shows "sum card ((λi. {{i, j} | j. j ∈ V ∧ {i, j} ∉ E}) ` V) ≤ card V * (card V * card V + card V)"
proof -
  have image_size: "∀i∈V. card ((λi. {{i, j} | j. j ∈ V ∧ {i, j} ∉ E}) i) ≤ (card V choose 2) + card V" using sp_image_elem_size f bruh_moment assms
    by fastforce
  have "card (⋃ ((λi. {{i, j} | j. j ∈ V ∧ {i, j} ∉ E}) ` V)) ≤ (∑i∈V. card ((λi. {{i, j} | j. j ∈ V ∧ {i, j} ∉ E}) i))"
    using assms card_UN_le ugraph_nodes_def by blast
  moreover have "... ≤ (∑i∈V. (card V choose 2) + card V)" using image_size
    by (meson sum_mono)
  moreover have "... ≤ card V * ((card V choose 2) + card V)" by auto
  moreover have "... ≤ card V * ((card V * (card V - 1) div 2) + card V)" by (simp add: choose_two)
  ultimately show ?thesis
    by (smt (verit, ccfv_SIG) add_le_cancel_right diff_le_self div_le_dividend le_trans mult_le_mono2)
qed

lemma card_bound:
assumes "ugraph_nodes E V"
shows "sum card ((λi. {{i, j} | j. j ∈ V ∧ {i, j} ∉ E}) ` V) ≤ (card E + card V) * ((card E + card V) * (card E + card V) + (card E + card V))"
using card_verteces[OF assms] by (meson add_mono_thms_linordered_semiring(1) dual_order.trans le_add2 mult_le_mono)

find_theorems "_ ≤ _ + _"

lemma clique_to_sp_size: "size_SP (clique_to_set_packing C) ≤ clique_to_set_packing_space (size_CLIQUE C)"
apply (auto simp: size_SP_def clique_to_set_packing clique_to_set_packing_space_def size_CLIQUE_def)
apply (cases C; simp)
using card_bound by blast

lemma clique_to_set_packing_refines: "clique_to_set_packing_poly C ≤ SPEC (λy. y = clique_to_set_packing C) (λ_. clique_to_set_packing_time (size_CLIQUE C))"
unfolding SPEC_def clique_to_set_packing_poly
  clique_to_set_packing mop_ugraph_nodes_def mop_set_image_sp_def size_CLIQUE_def
apply(rule T_specifies_I)
apply(vcg' \<open>-\<close> rules: T_SPEC)
by (auto simp: clique_to_set_packing_time_def one_enat_def mult_le_mono)

theorem clique_to_set_packing_ispolyred: "ispolyred clique_to_set_packing_poly clique set_packing size_CLIQUE size_SP"
unfolding ispolyred_def
apply(rule exI[where x=clique_to_set_packing])
apply(rule exI[where x=clique_to_set_packing_time])
apply(rule exI[where x=clique_to_set_packing_space])
apply safe
  subgoal using clique_to_set_packing_refines by blast
  subgoal using clique_to_sp_size by blast
  subgoal unfolding poly_def clique_to_set_packing_time_def apply(rule exI[where x=3]) by auto
  subgoal unfolding poly_def clique_to_set_packing_space_def apply(rule exI[where x=3]) by auto
  subgoal using is_reduction_clique_to_set_packing .
done

end
