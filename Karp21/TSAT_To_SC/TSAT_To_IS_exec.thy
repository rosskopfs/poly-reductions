theory TSAT_To_IS_exec
  imports TSAT_To_IS Poly_Reductions_Lib.SAT_Definition_exec IS_Definition_exec Poly_Reductions_Lib.Tr_Fun_Defs
begin

subsection \<open>Executable Three Sat to Independent Set\<close>

unbundle lifting_syntax

lemma map_image_rel[transfer_rule]: "((r ===> s) ===> Set_List_rel r ===> Set_List_rel s) image map"
  by (fastforce simp: rel_set_def dest: rel_funD)

lemma Sprod_Lprod_rel[transfer_rule]: "(Set_List_rel_eq ===> Set_List_rel_eq ===> Set_List_rel_eq) (\<times>) List.product"
  by fastforce

lemma UN_set_concat_rel[transfer_rule]: "(list_all2 (Set_List_rel r) ===> (Set_List_rel r)) (\<lambda>s. \<Union> (set s)) concat"
  by (fastforce simp: in_set_conv_nth list_all2_conv_all_nth rel_set_def)

lemma filter_pred_rel[transfer_rule]: "(Set_List_rel_eq ===> Set_List_rel (\<lambda>a b. a = b \<and> p a)) (Set.filter p) (filter p)"
  by (fastforce intro: rel_setI simp: rel_set_eq)

lemma union_append_rel[transfer_rule]: "(Set_List_rel r ===> Set_List_rel r ===> Set_List_rel r) (\<union>) (@)"
  by (fastforce simp: rel_set_def)

lemma Ball_set_list_all_rel[transfer_rule]: "((r ===> (=)) ===> list_all2 r ===> (=)) (\<lambda>p F. Ball (set F) p) list_all"
  by (fastforce simp: in_set_conv_nth list_all2_conv_all_nth list_all_length dest: rel_funD)

lemma id_set_rel[transfer_rule]: "(Set_List_rel r ===> rel_set r) (\<lambda>x. x) set"
  by blast


subsubsection \<open>executable definition of \<open>sat_is_un_1\<close>\<close>

definition
  "sat_is_un_1_exec F \<equiv>
    let
      p1 = enumerate 0 F;
      p2 = map (\<lambda>(xsa, xsb). map (\<lambda>x. (x, xsa)) xsb) p1;
      p3 = map (\<lambda>xs. List.product xs xs) p2;
      p4 = map (\<lambda>xs. filter (\<lambda>((a, _), (b, _)). a \<noteq> b) xs) p3;
      p5 = concat p4;
      p6 = map (\<lambda>(a, b). [a, b]) p5
    in p6"

text \<open>definition equivalent to \<open>sat_is_un_1\<close> for easier proof of relation\<close>
definition
  "sat_is_un_1'_prod F \<equiv>
    let
      p1 = enumerate 0 F;
      p2 = map (\<lambda>(i, xsb). (\<lambda>x. (x, i)) ` xsb) p1;
      p3 = map (\<lambda>s. s \<times> s) p2;
      p4 = map (\<lambda>s. Set.filter (\<lambda>((a, _), (b, _)). a \<noteq> b) s) p3;
      p5 = \<Union> (set p4)
    in p5"

definition
  "sat_is_un_1' F \<equiv> (\<lambda>(a, b). {a, b}) ` (sat_is_un_1'_prod F)"

lemma sat_is_un_1'_eq: "sat_is_un_1 F = sat_is_un_1' F"
  unfolding sat_is_un_1_def sat_is_un_1'_def sat_is_un_1'_prod_def
  by (fastforce simp: in_set_enumerate_eq)
lemmas sat_is_un_1'_eq_unfold = sat_is_un_1'_eq[unfolded sat_is_un_1'_def sat_is_un_1'_prod_def]

text \<open>\<open>sat_is_un_1_exec\<close> is related to \<open>sat_is_un_1\<close>\<close>
lemma sat_is_un_1_rel[transfer_rule]: "(list_all2 (Set_List_rel_eq) ===> Set_List_rel Set_List_rel_eq) sat_is_un_1 sat_is_un_1_exec"
proof -
  have [transfer_rule]: "(list_all2 (Set_List_rel_eq) ===> list_all2 (rel_prod (=) (Set_List_rel_eq)))
      (enumerate 0) (enumerate 0)"
    by (auto simp: list_all2_conv_all_nth nth_enumerate_eq)
  have [transfer_rule]: "(list_all2 (rel_prod (=) (Set_List_rel_eq)) ===> list_all2 (Set_List_rel_eq))
    (map (\<lambda>(a, b). (\<lambda>x. (x, a)) ` b))
    (map (\<lambda>(a, b). map (\<lambda>x. (x, a)) b))" (is "(list_all2 ?A2 ===> list_all2 ?B2) (map ?fs2) (map ?fl2)")
  proof -
    define fs fl where def: "fs = ?fs2" "fl = ?fl2"
    have [transfer_rule]: "(?A2 ===> ?B2) fs fl"
      by (fastforce simp: rel_set_eq inj_on_def card_image def)
    show ?thesis
      unfolding def[symmetric] by transfer_prover
  qed
  have [transfer_rule]: "(list_all2 (Set_List_rel_eq) ===> list_all2 (Set_List_rel_eq))
      (map (\<lambda>s. s \<times> s)) (map (\<lambda>l. List.product l l))"
    by transfer_prover
  have [transfer_rule]: "(list_all2 (Set_List_rel_eq) ===> list_all2 (Set_List_rel (\<lambda>a b. a = b \<and> fst (fst a) \<noteq> fst (snd a))))
    (map (Set.filter (\<lambda>((a, _), (b, _)). a \<noteq> b)))
    (map (filter (\<lambda>((a, _), (b, _)). a \<noteq> b)))"
    (is "(list_all2 _ ===> list_all2 (Set_List_rel ?B4)) (map (Set.filter ?f4)) (map (filter ?f4))")
  proof (intro rel_funI) fix x y
    define f B where def: "f = ?f4" "B = ?B4"
    have "B = (\<lambda>a b. a = b \<and> f a)"
      unfolding def by auto
    then have [transfer_rule]: "(Set_List_rel_eq ===> Set_List_rel B) (Set.filter f) (filter f)"
      using filter_pred_rel by auto
    have aux: "(list_all2 Set_List_rel_eq ===> list_all2 (Set_List_rel B)) (map (Set.filter f)) (map (filter f))"
      by transfer_prover
    then show "list_all2 (Set_List_rel_eq) x y \<Longrightarrow> list_all2 (Set_List_rel ?B4)
        (map (Set.filter ?f4) x) (map (filter ?f4) y)"
      using rel_fun_mono[OF aux, where Y="list_all2 Set_List_rel_eq" and B="list_all2 (Set_List_rel B)"] list_all2_mono
      unfolding def[symmetric] rel_fun_def by blast
  qed
  have [transfer_rule]: "(list_all2 (Set_List_rel (\<lambda>a b. a = b \<and> fst (fst a) \<noteq> fst (snd a))) ===>
        Set_List_rel (\<lambda>a b. a = b \<and> fst (fst a) \<noteq> fst (snd a))) (\<lambda>s. \<Union> (set s)) concat"
    by transfer_prover
  have [transfer_rule]: "(Set_List_rel (\<lambda>a b. a = b \<and> fst (fst a) \<noteq> fst (snd a)) ===> Set_List_rel Set_List_rel_eq)
    (image (\<lambda>(a, b). {a, b}))
    (map (\<lambda>(a, b). [a, b]))" (is "(Set_List_rel ?A6 ===> Set_List_rel ?B6) (image ?fs6) (map ?fl6)")
  proof -
    define fs fl where def: "fs = ?fs6" "fl = ?fl6"
    have [transfer_rule]: "(?A6 ===> ?B6) fs fl"
      by (auto simp: def rel_fun_def rel_set_def)
    show ?thesis
      unfolding def[symmetric] by transfer_prover
  qed
  show ?thesis
    unfolding sat_is_un_1'_eq_unfold sat_is_un_1_exec_def Let_def
    by transfer_prover
qed


subsubsection \<open>executable definition of \<open>sat_is_un_2\<close>\<close>

text \<open>executable definition of \<open>conflict\<close>\<close>
definition
  "conflict_exec a1 a2 \<equiv> case (a1, a2) of
    (Pos a1', Neg a2') \<Rightarrow> a1' = a2'
  | (Neg a1', Pos a2') \<Rightarrow> a1' = a2'
  | (_, _) \<Rightarrow> False"

lemma conflict_exec_eq_conflict: "conflict_exec = conflict"
  by (auto simp: fun_eq_iff conflict_exec_def conflict_def split: lit.split)

definition
  "sat_is_un_2_exec F \<equiv>
    let
      p1 = enumerate 0 F;
      p2 = map (\<lambda>(xsa, xsb). map (\<lambda>x. (x, xsa)) xsb) p1;
      p3 = List.product p2 p2;
      p4 = map (\<lambda>(a, b). List.product a b) p3;
      p5 = concat p4;
      p6 = filter (\<lambda>((a, _), (b, _)). conflict_exec a b) p5;
      p7 = map (\<lambda>(a, b). [a, b]) p6
    in p7"

text \<open>definition equivalent to \<open>sat_is_un_2\<close> for easier proof of relation\<close>
definition
  "sat_is_un_2'_prod F \<equiv>
    let
      p1 = enumerate 0 F;
      p2 = map (\<lambda>(xsa, xsb). (\<lambda>x. (x, xsa)) ` xsb) p1;
      p3 = List.product p2 p2;
      p4 = map (\<lambda>(a, b). a \<times> b) p3;
      p5 = \<Union> (set p4);
      p6 = Set.filter (\<lambda>((a, _), (b, _)). conflict a b) p5
    in p6"
definition
  "sat_is_un_2' F \<equiv> (\<lambda>(a, b). {a, b}) ` sat_is_un_2'_prod F"

lemma sat_is_un_2'_eq: "sat_is_un_2 F = sat_is_un_2' F"
  unfolding sat_is_un_2_def sat_is_un_2'_def sat_is_un_2'_prod_def Let_def
  by (fastforce simp: in_set_enumerate_eq)
lemmas sat_is_un_2'_eq_unfold = sat_is_un_2'_eq[unfolded sat_is_un_2'_def sat_is_un_2'_prod_def]

text \<open>\<open>sat_is_un_2_exec\<close> is related to \<open>sat_is_un_2\<close>\<close>
lemma sat_is_un_2_rel[transfer_rule]: "(list_all2 Set_List_rel_eq ===> Set_List_rel Set_List_rel_eq) sat_is_un_2 sat_is_un_2_exec"
proof -
  have [transfer_rule]: "(list_all2 (Set_List_rel_eq) ===> list_all2 (rel_prod (=) (Set_List_rel_eq)))
      (enumerate 0) (enumerate 0)"
    by (auto simp: list_all2_conv_all_nth nth_enumerate_eq)
  have [transfer_rule]: "(list_all2 (rel_prod (=) (Set_List_rel_eq)) ===> list_all2 (Set_List_rel_eq))
      (map (\<lambda>(a, b). (\<lambda>x. (x, a)) ` b))
      (map (\<lambda>(a, b). map (\<lambda>x. (x, a)) b))" (is "(list_all2 ?A2 ===> list_all2 ?B2) (map ?fs2) (map ?fl2)")
  proof -
    define fs fl where def: "fs = ?fs2" "fl = ?fl2"
    have [transfer_rule]: "(?A2 ===> ?B2) fs fl"
      by (fastforce simp: rel_set_eq inj_on_def card_image def)
    show ?thesis
      unfolding def[symmetric] by transfer_prover
  qed
  have [transfer_rule]: "(list_all2 (Set_List_rel_eq) ===> list_all2 (rel_prod (Set_List_rel_eq) (Set_List_rel_eq)))
      (\<lambda>x. List.product x x) (\<lambda>x. List.product x x)"
    by transfer_prover
  have [transfer_rule]: "(list_all2 (rel_prod (Set_List_rel_eq) (Set_List_rel_eq)) ===> list_all2 (Set_List_rel_eq))
      (map (\<lambda>(a, b). a \<times> b)) (map (\<lambda>(a, b). List.product a b))"
    by transfer_prover
  have [transfer_rule]: "(list_all2 Set_List_rel_eq ===> Set_List_rel_eq) (\<lambda>s. \<Union> (set s)) concat"
    by transfer_prover
  have [transfer_rule]: "(Set_List_rel_eq ===> Set_List_rel (\<lambda>a b. a = b \<and> conflict (fst (fst a)) (fst (snd a))))
      (Set.filter (\<lambda>((a, _), (b, _)). conflict a b)) (filter (\<lambda>((a, _), (b, _)). conflict a b))"
    using filter_pred_rel by (fastforce simp: case_prod_beta')
  have [transfer_rule]: "(Set_List_rel (\<lambda>a b. a = b \<and> conflict (fst (fst a)) (fst (snd a))) ===> Set_List_rel Set_List_rel_eq)
      (image (\<lambda>(a, b). {a, b})) (map (\<lambda>(a, b). [a, b]))" (is "(Set_List_rel ?A7 ===> Set_List_rel ?B7) (image ?fs7) (map ?fl7)")
  proof -
    define fs fl where def: "fs = ?fs7" "fl = ?fl7"
    have "conflict (fst (fst a)) (fst (snd a)) \<Longrightarrow> (fst a) \<noteq> (snd a)" for a::"('b lit \<times> 'c) \<times> ('b lit \<times> 'c)"
      by auto
    then have [transfer_rule]: "(?A7 ===> ?B7) fs fl"
      by (fastforce simp: def rel_fun_def rel_set_def)
    show ?thesis
      unfolding def[symmetric] by transfer_prover
  qed
  show ?thesis
    unfolding sat_is_un_2'_eq_unfold sat_is_un_2_exec_def conflict_exec_eq_conflict Let_def
    by transfer_prover
qed


subsubsection \<open>executable definition of \<open>sat_is\<close>\<close>

definition
  "sat_is_exec F \<equiv> if list_all (\<lambda>xs. length (remdups xs) = 3) F
    then (sat_is_un_1_exec F @ sat_is_un_2_exec F, length F)
    else ([], 1)"
lemmas sat_is_exec_unfold = sat_is_exec_def[unfolded sat_is_un_1_exec_def sat_is_un_2_exec_def]

text \<open>\<open>sat_is_exec\<close> is related to \<open>sat_is\<close>\<close>
lemma sat_is_exec_rel[transfer_rule]: "(list_all2 Set_List_rel_eq ===> IS_List_rel) sat_is sat_is_exec"
proof -
  have [transfer_rule]: "rel_prod (Set_List_rel Set_List_rel_eq) (=) ({}, 1) ([], 1)"
    by (simp add: rel_set_def)
  show ?thesis
    unfolding sat_is_def sat_is_exec_def IS_List_rel_iff
    by transfer_prover
qed


subsubsection \<open>tail recursive definition of \<open>sat_is_exec\<close>\<close>

text \<open>tail recursive definition of \<open>sat_is_un_1_exec\<close>\<close>
definition
  "sat_is_un_1_exec_tr F \<equiv>
    let
      p1 = enumerate_tr 0 F;
      p2 = map_tr (\<lambda>(xsa, xsb). map_tr (\<lambda>x. (x, xsa)) xsb) p1;
      p3 = map_tr (\<lambda>xs. product_tr xs xs) p2;
      p4 = map_tr (\<lambda>xs. filter_tr (\<lambda>((a, _), (b, _)). a \<noteq> b) xs) p3;
      p5 = concat_tr p4;
      p6 = map_tr (\<lambda>(a, b).  [a, b]) p5
    in p6"

lemma sat_is_un_1_exec_tr_eq: "sat_is_un_1_exec_tr = sat_is_un_1_exec"
  unfolding sat_is_un_1_exec_tr_def sat_is_un_1_exec_def tr_simps
  by (rule refl)

text \<open>tail recursive definition of \<open>sat_is_un_2_exec\<close>\<close>
definition
  "sat_is_un_2_exec_tr F \<equiv>
    let
      p1 = enumerate_tr 0 F;
      p2 = map_tr (\<lambda>(xsa, xsb). map_tr (\<lambda>x. (x, xsa)) xsb) p1;
      p3 = product_tr p2 p2;
      p4 = map_tr (\<lambda>(a, b). product_tr a b) p3;
      p5 = concat_tr p4;
      p6 = filter_tr (\<lambda>((a, _), (b, _)). conflict_exec a b) p5;
      p7 = map_tr (\<lambda>(a, b). [a, b]) p6
    in p7"

lemma sat_is_un_2_exec_tr_eq: "sat_is_un_2_exec_tr = sat_is_un_2_exec"
  unfolding sat_is_un_2_exec_tr_def sat_is_un_2_exec_def tr_simps
  by (rule refl)

definition
  "sat_is_exec_tr F \<equiv> if list_all_tr (\<lambda>xs. length_tr (remdups_tr xs) = 3) F
    then (sat_is_un_1_exec_tr F @tr sat_is_un_2_exec_tr F, length_tr F)
    else ([], 1)"

lemma "sat_is_exec_tr = sat_is_exec"
  unfolding sat_is_exec_tr_def sat_is_exec_def sat_is_un_1_exec_tr_eq sat_is_un_2_exec_tr_eq tr_simps
  by (rule refl)


subsection \<open>\<open>sat_is_exec\<close> is a reduction from \<open>three_cnf_sat\<close> to \<open>independent_set\<close>\<close>

lemma IS_p_exec_sat_is_exec_if_TSAT_p_exec:
  assumes "three_cnf_sat_pred_exec F"
  shows "independent_set_pred_exec (sat_is_exec F)"
proof -
  have [transfer_rule]: "list_all2 Set_List_rel_eq (transl_SAT_list_set F) F"
    using transl_SAT_list_set_rel .
  from assms have "three_cnf_sat_pred (transl_SAT_list_set F)"
    using TSAT_p_exec_TSAT_p_transl_iff by blast
  then have "independent_set_pred (sat_is (transl_SAT_list_set F))"
    using is_reduction_sat_is[unfolded is_reduction_def three_cnf_sat_unfold_pred independent_set_unfold_pred] by blast
  show "independent_set_pred_exec (sat_is_exec F)"
    by transfer (fact \<open>independent_set_pred (sat_is (transl_SAT_list_set F))\<close>)
qed

lemma TSAT_p_exec_if_IS_p_exec_sat_is_exec:
  assumes "independent_set_pred_exec (sat_is_exec x)" (is ?asm)
  shows "three_cnf_sat_pred_exec x"
proof -
  have [transfer_rule]: "list_all2 Set_List_rel_eq (transl_SAT_list_set x) x"
    using transl_SAT_list_set_rel .
  have "independent_set_pred (sat_is (transl_SAT_list_set x)) \<longleftrightarrow> ?asm"
    by transfer_prover
  with assms have "independent_set_pred (sat_is (transl_SAT_list_set x))" by simp
  then have "three_cnf_sat_pred (transl_SAT_list_set x)"
    using is_reduction_sat_is[unfolded is_reduction_def three_cnf_sat_unfold_pred independent_set_unfold_pred] by blast
  then show ?thesis
    using TSAT_p_exec_TSAT_p_transl_iff by blast
qed

lemma is_reduction_sat_is_exec: "is_reduction sat_is_exec three_cnf_sat_exec independent_set_exec"
  unfolding is_reduction_def three_cnf_sat_exec_def independent_set_exec_def
  using IS_p_exec_sat_is_exec_if_TSAT_p_exec TSAT_p_exec_if_IS_p_exec_sat_is_exec by blast

end