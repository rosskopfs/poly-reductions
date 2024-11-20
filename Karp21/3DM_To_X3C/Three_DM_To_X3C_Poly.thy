theory Three_DM_To_X3C_Poly
  imports "../Polynomial_Reductions" Three_DM_To_X3C "HOL-Library.Disjoint_Sets" 
begin


definition "size_TDM = (\<lambda>(U, T). card T + 3 * card U + 1)" 
definition "size_X3C = (\<lambda>(X, S). card X + 3 * card S + 1)"

definition "mop_set_image_const_cost f S f_cost  = SPECT [f ` S \<mapsto> f_cost * card S]"
definition "mop_set_union S1 S2 = SPECT [S1 \<union> S2 \<mapsto> card S1 + card S2]"

definition tdm_to_x3c_alg where
  "tdm_to_x3c_alg = (\<lambda>(U, T). do {
    X_a \<leftarrow> mop_set_image_const_cost a T 1;
    X_b \<leftarrow> mop_set_image_const_cost b T 1;
    X_c \<leftarrow> mop_set_image_const_cost c T 1;
    X_ab \<leftarrow> mop_set_union X_a X_b;
    X \<leftarrow> mop_set_union X_ab X_c;
    S \<leftarrow> mop_set_image_const_cost (\<lambda>(x, y, z). {a x, b y, c z}) U 3;
    RETURNT (X, S)
  })"


definition "tdm_to_x3c_time n = 8 * n"  (* 8 * card T + 3 * card U \<le> 8 * size_TDM (U,T) *)
definition "tdm_to_x3c_space n = 3 * n"


lemma tdm_to_x3c_refines:
  "tdm_to_x3c_alg P 
  \<le> SPEC (\<lambda>y. y = three_dm_to_x3c P) (\<lambda>_. tdm_to_x3c_time (size_TDM P))"
  unfolding SPEC_def tdm_to_x3c_alg_def three_dm_to_x3c_def 
    mop_set_image_const_cost_def  mop_set_union_def tdm_to_x3c_time_def
    size_TDM_def
  apply(rule T_specifies_I)
  apply(vcg' \<open>-\<close> rules: T_SPEC )
  by (auto intro!: card_Un_le[THEN le_trans] simp add: card_image inj_on_def )


lemma abc_tag_img: "{{a x, b y, c z} |x y z. (x, y, z) \<in> U} = 
      (\<lambda>x. case x of (x, y, z) \<Rightarrow> {a x, b y, c z}) ` U"
  by auto

lemma "3 * card {{a x, b y, c z} |x y z. (x, y, z) \<in> U} = 3 * card U"
  by (auto intro!: card_image[unfolded inj_on_def] simp add: abc_tag_img)
 

lemma tdm_to_x3c_size:
  "size_X3C (three_dm_to_x3c (U, T)) \<le> tdm_to_x3c_space (size_TDM (U, T))"
  
proof -
  have abc_tag_img: "{{a x, b y, c z} |x y z. (x, y, z) \<in> U} = 
    (\<lambda>x. case x of (x, y, z) \<Rightarrow> {a x, b y, c z}) ` U"
    by auto
  then have "card {{a x, b y, c z} |x y z. (x, y, z) \<in> U} = card U"
    by (auto intro!: card_image[unfolded inj_on_def] simp add: abc_tag_img)
  moreover have "card ((a `T) \<union> (b `T) \<union> (c `T)) \<le> card T + card T + card T"
    by (auto intro!: card_Un_le[THEN le_trans]
                     card_image[THEN eq_refl, THEN add_le_mono[rotated]]
             simp add: card_image inj_on_def)
  ultimately show ?thesis
    unfolding size_X3C_def three_dm_to_x3c_def tdm_to_x3c_space_def size_TDM_def
    by auto
qed


theorem tdm_to_x3c_is_polyred:
  "ispolyred tdm_to_x3c_alg three_d_matching three_exact_cover size_TDM size_X3C"
  using tdm_to_x3c_refines tdm_to_x3c_size  is_reduction_three_dm_to_x3c 
        poly_cmult poly_linear
  by (intro ispolyredI[where ?time_f  = tdm_to_x3c_time  and
                             ?space_f = tdm_to_x3c_space],
      unfold tdm_to_x3c_time_def tdm_to_x3c_space_def) fast+
end