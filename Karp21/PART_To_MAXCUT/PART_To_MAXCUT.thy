theory PART_To_MAXCUT
  imports
    "HOL.Quotient"
    Undirected_Graph_Theory.Undirected_Graphs_Root
    Reductions
begin

definition max_cut  where
  "max_cut \<equiv> {((V,E), w, W).
                       fin_sgraph V E \<and>
                       (\<exists>S. S \<subseteq> V  \<and> sum w {{u, v}|u v. u \<in> S \<and> v \<in> (V - S)} \<ge> W)}"
find_consts name:comm_semiring

lemma max_cut_cert:
  assumes "S \<subseteq> V"
    "sum w {{u, v}|u v. u \<in> S \<and> v \<in> (V - S)} \<ge> W"
    "fin_sgraph V E"
  shows "  ((V,E), w, W) \<in> max_cut"
  unfolding max_cut_def
  using assms
  by blast

definition "part_alter \<equiv> {as::nat list. \<exists>xs. (\<forall>i < length xs. xs!i \<in> {0, 1}) \<and> length as = length xs
  \<and> (\<Sum>i < length as. as ! i * xs ! i) = (\<Sum>i < length as. as ! i * (1 - xs ! i))}"

(* the reduction in Karp's paper used ceil (1/4 sum of squares) but that doesn't work
   consider for example [1, 2, 2], 1 + 2 \<noteq> 2
   but (1 * 2 + 2 * 2) \<ge> (ceil (1/4 * (2^2 + 2^2 + 1)) *)

abbreviation "w as \<equiv> (\<lambda>s. (THE x. x \<in> {(as!u) * (as!v)|u v. {u, v} = s}))"
definition part_to_max_cut  where
  "part_to_max_cut as = (({..<length as},all_edges {..<length as}),
                          w as, (sum_list as^2 + 3) div 4)"

lemma reduction_weight_is_product:
  assumes "finite S"
  shows "sum (w (as::nat list)) {{u, v}|u v. u \<in> S \<and> v \<in> ({..<length as} - S)}
        = (\<Sum>i\<in>S. as!i) * (\<Sum>j\<in>({..<length as} - S). as!j)"
proof -
  let ?V = "{..<length as}"
  have "sum (w as) {{u, v}|u v. u \<in> S \<and> v \<in> (?V - S)}
            = sum (w as) (\<Union> ((\<lambda>u. (\<lambda>v. {u, v}) ` (?V - S)) ` S))"
    by (auto intro!: sum.cong)+
  also have "\<dots> = (\<Sum>x\<in>S. sum (w as) ( (\<lambda>u. (\<lambda>v. {u, v}) ` (?V - S)) x))"
    using finite_M_bounded_by_nat \<open>finite S\<close>
    by (intro Groups_Big.comm_monoid_add_class.sum.UNION_disjoint) auto
  also have "... = (\<Sum>x\<in>S. sum ((w as) \<circ> (\<lambda>v. {x, v})) (?V - S))"
    by (intro sum.cong sum.reindex)
      (auto  simp add: inj_on_def doubleton_eq_iff)
  also have "... = (\<Sum>i\<in>S. \<Sum>j\<in>(?V - S). (w as) {i,j})"
    by auto
  also have "... = (\<Sum>i\<in>S. \<Sum>j\<in>(?V - S).  as!i * as!j)"
    by (auto intro!: sum.cong the1_equality simp add: doubleton_eq_iff)
  also have "... = (\<Sum>i\<in>S. as!i) * (\<Sum>j\<in>(?V - S). as!j)"
    by (simp add: sum_product)
  finally show ?thesis.
qed

lemma square_diff_square_factored':
  "(x::'a::comm_semiring_1_cancel)*x - y*y = (x+y)*(x-y)"
proof -
  have "(x+y)*(x-y) = (x+y)*x - (x+y)*y"
    by (simp add: right_diff_distrib')
  also have "... = (x*x + x*y) - (x*y + y*y)"
    by (simp add: distrib_left mult.commute)
  also have "... = x*x - y*y"
    by (metis add_diff_cancel_right' diff_diff_eq)
  finally show ?thesis
    by argo
qed

lemma sq_sum_ge_4xy1_if_ge:
  assumes "(x::nat) > y"
  shows "(x + y)^2 \<ge> 4*x*y + 1"
proof -
  have "4*x*y + 1 \<le> 4*x*y + (x-y)*(x-y)"
    using assms by auto
  also have *: "\<dots>  = (x+y)*(x+y) - (x-y)*(x-y) + (x-y)*(x-y)"
    by (auto simp add: square_diff_square_factored'[of "x+y" "x-y"]
        ,simp add: assms distrib_left less_or_eq_imp_le mult.commute)
  also have "...  = (x+y)*(x+y)"
    by (metis diff_le_self le_add_diff_inverse2 mult_le_mono trans_le_add1)
  finally show ?thesis
    by (simp add: power2_eq_square)
qed

lemma xy_ge_ceil_div4_of_sum_sq_iff_eq:
  "(x::nat) * y \<ge> ((x + y)^2 + 3) div 4 \<longleftrightarrow> x = y"
proof
  show "((x + y)\<^sup>2 + 3) div 4 \<le> x * y \<Longrightarrow> x = y"
  proof (rule ccontr)
    assume *:"x * y \<ge> ((x + y)^2 + 3) div 4"
    assume "x \<noteq> y"
    then have "(x + y)^2 \<ge> 4*x*y + 1"
      using sq_sum_ge_4xy1_if_ge[of y x]   sq_sum_ge_4xy1_if_ge[of x y]
      by (cases "x > y") (auto simp add: add.commute mult.commute mult.left_commute)
    then have "((x + y)^2 + 3) div 4 \<ge> x*y + 1"
      by auto
    then show False
      using * by auto
  qed
  have "((y + y)\<^sup>2 + 3) div 4 = (4*y^2 + 3) div 4"
    by (metis mult_2 numeral_Bit0 power2_eq_square power_mult_distrib)
  also have "... = y^2" by auto
  finally show "x = y \<Longrightarrow> ((x + y)\<^sup>2 + 3) div 4 \<le> x * y"
    by (simp add: power2_eq_square)
qed


lemma part_to_max_cut_sound:
  assumes "as \<in> part_alter"
  shows "part_to_max_cut as \<in> max_cut"
proof -
  obtain xs where "(\<forall>i < length xs. xs!i \<in> {0, 1})"
    and   "length as = length xs"
    and   "(\<Sum>i < length as. as ! i * xs ! i)
                  = (\<Sum>i < length as. as ! i * (1 - xs ! i))"
    using assms unfolding part_alter_def
    by blast

  let ?W = "(sum_list as^2 + 3) div 4"
  let ?V = "{..<length as}"
  define S where "S = {x \<in> {..<length as}. xs ! x = 1}"


  have "((?V,all_edges ?V), w as, ?W) \<in> max_cut"
  proof (intro max_cut_cert[of S])
    show "S \<subseteq> {..<length as}"
      using S_def by auto
    then have "finite S"
      using finite_subset by blast

    show "fin_sgraph ?V (all_edges ?V)"
      by (unfold_locales) blast

    have "sum (w as) {{u, v}|u v. u \<in> S \<and> v \<in> (?V - S)}
            = (\<Sum>i\<in>S. as!i) * (\<Sum>j\<in>(?V - S). as!j)"
      using reduction_weight_is_product \<open>finite S\<close>
      by auto
    also have "... \<ge> (((\<Sum>i\<in>S. as!i) + (\<Sum>j\<in>(?V - S). as!j))^2 + 3) div 4"
    proof (intro xy_ge_ceil_div4_of_sum_sq_iff_eq[THEN iffD2])
      have "(\<Sum>i\<in>S. as!i) = (\<Sum>i<length as. if xs!i = 1 then as!i else 0)"
        unfolding S_def
        by (intro sum.inter_filter) auto
      also have "\<dots> = (\<Sum>i<length as. as!i * xs!i)"
        using \<open>\<forall>i<length xs. xs ! i \<in> {0, 1}\<close> \<open>length as = length xs\<close>
        by (intro sum.cong) auto
      finally have sum_S: "(\<Sum>i\<in>S. as!i) = (\<Sum>i<length as. as!i * xs!i)".
      also have "... = (\<Sum>i < length as. as ! i * (1 - xs ! i))"
        using \<open>(\<Sum>i<length as. as ! i * xs ! i) = (\<Sum>i<length as. as ! i * (1 - xs ! i))\<close> .
      also have "... = (\<Sum>i < length as. as ! i  - as!i *  xs ! i)"
        by (auto intro: sum.cong simp add: diff_mult_distrib2)
      also have "... = (\<Sum>i < length as. as ! i ) - (\<Sum>i < length as. as ! i * xs ! i)"
        using \<open>\<forall>i<length xs. xs ! i \<in> {0, 1}\<close> \<open>length as = length xs\<close>
        by (intro sum_subtractf_nat) auto
      also have  "... = (\<Sum>j\<in>(?V - S). as!j)"
        using sum_diff_nat sum_S  \<open>S \<subseteq> {..<length as}\<close> \<open>finite S\<close>
        by fastforce
      finally show "(\<Sum>i\<in>S. as!i) = (\<Sum>j\<in>(?V - S). as!j)".
    qed
    finally show "sum (w as) {{u, v}|u v. u \<in> S \<and> v \<in> (?V - S)}
                  \<ge>  ((sum_list as )^2 + 3) div 4"
      using sum.subset_diff[OF \<open>S \<subseteq> {..<length as}\<close> finite_lessThan, of "(!) as"]
      by (simp add: add.commute atLeast_upt sum_list_sum_nth)
  qed
  then show ?thesis
    unfolding part_to_max_cut_def
    by blast
qed


lemma part_to_max_cut_complete:
  assumes "part_to_max_cut as \<in> max_cut"
  shows "as \<in> part_alter"
proof -
  let ?W = "(sum_list as^2 + 3) div 4"
  let ?V = "{..<length as}"
  obtain S where "fin_sgraph ?V (all_edges ?V)"
    "S \<subseteq> ?V"
    "sum (w as) {{u, v}|u v. u \<in> S \<and> v \<in> (?V - S)} \<ge> ?W"
    using assms unfolding max_cut_def part_to_max_cut_def
    by blast

  define xs where "xs = map (\<lambda>i. if i \<in> S then 1::nat else 0) [0..<length as]"
  have xs01: "\<forall>i<length xs. xs ! i \<in> {0, 1}"
    using xs_def
    by simp
  moreover have len_xs:"length as = length xs"
    using xs_def
    by simp
  moreover{
    have "(\<Sum>i<length as. as ! i * xs ! i) = (\<Sum>i<length as. if i \<in> S then as!i else 0)"
      using xs01 len_xs xs_def
      by (intro sum.cong) fastforce+
    also have "\<dots> = (\<Sum>i\<in>(?V \<inter> S). as!i)"
      by (intro sum.inter_restrict[symmetric]) auto
    finally have eq1:"(\<Sum>i<length as. as ! i * xs ! i) = (\<Sum>i\<in>S. as!i)"
      using \<open>S \<subseteq> ?V\<close>
      by (simp add: inf_absorb2)

    have "(\<Sum>i < length as. as ! i * (1 - xs ! i))
         = (\<Sum>i<length as. if i \<in> (?V - S) then as!i else 0)"
      using xs01 len_xs xs_def
      by (intro sum.cong) fastforce+
    also have "\<dots> = (\<Sum>i\<in>(?V \<inter> (?V - S)). as!i)"
      by (intro sum.inter_restrict[symmetric]) auto
    finally have eq2: "(\<Sum>i < length as. as ! i * (1 - xs ! i)) = (\<Sum>i\<in>(?V - S). as!i)"
      using \<open>S \<subseteq> ?V\<close>
      by (simp add: inf_absorb2)

    have "finite S"
      using \<open>S \<subseteq> {..<length as}\<close> infinite_super by blast
    then have "(\<Sum>i\<in>S. as!i)  * (\<Sum>i\<in>(?V - S). as!i) \<ge> ?W"
      using  reduction_weight_is_product
        \<open>sum (w as) {{u, v}|u v. u \<in> S \<and> v \<in> (?V - S)} \<ge> ?W\<close>
      by presburger
    then have "(\<Sum>i\<in>S. as!i) = (\<Sum>i\<in>(?V - S). as!i)"
      using  xy_ge_ceil_div4_of_sum_sq_iff_eq
      by (metis \<open>S \<subseteq> {..<length as}\<close>
          add.commute atLeast_upt finite_lessThan set_upt sum.subset_diff sum_list_sum_nth)
    then have "(\<Sum>i<length as. as ! i * xs ! i) = (\<Sum>i < length as. as ! i * (1 - xs ! i))"
      using eq1 eq2 by argo
  }
  ultimately show ?thesis
    unfolding part_alter_def
    by blast
qed

theorem is_reduction_part_to_maxcut: "is_reduction part_to_max_cut part_alter max_cut"
  using part_to_max_cut_sound  part_to_max_cut_complete
  by (intro is_reductionI) auto

end
