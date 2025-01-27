\<^marker>\<open>creator "Nico Lintner"\<close>
\<^marker>\<open>contributor "Kevin Kappelmann"\<close>
subsection \<open>Three Sat to Independent Set on Lists\<close>
theory THREE_SAT_To_IS_List
  imports
    IS_Definition_List
    THREE_SAT_To_IS
begin

subsubsection \<open>List Definition of @{term sat_is_un_1}\<close>

definition
  "sat_is_un_1_list F \<equiv>
    let
      p1 = enumerate 0 F;
      p2 = map (\<lambda>(xsa, xsb). map (\<lambda>x. (x, xsa)) xsb) p1;
      p3 = map (\<lambda>xs. List.product xs xs) p2;
      p4 = map (\<lambda>xs. filter (\<lambda>((a, _), (b, _)). a \<noteq> b) xs) p3;
      p5 = concat p4;
      p6 = map (\<lambda>(a, b). [a, b]) p5
    in p6"

text \<open>Definition equivalent to @{term sat_is_un_1} and closer to @{term sat_is_un_1_list}.\<close>

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

lemma sat_is_un_1_eq_sat_is_un_1': "sat_is_un_1 F = sat_is_un_1' F"
  unfolding sat_is_un_1_def sat_is_un_1'_def sat_is_un_1'_prod_def
  by (fastforce simp: in_set_enumerate_eq)

lemmas sat_is_un_1_eq_sat_is_un_1'_unfold =
  sat_is_un_1_eq_sat_is_un_1'[unfolded sat_is_un_1'_def sat_is_un_1'_prod_def]

text \<open>@{term sat_is_un_1} is related to @{term sat_is_un_1_list}.\<close>

lemma rel_fun_sat_is_un_1_sat_is_un_1_list [transfer_rule]:
  "(list_all2 (Set_List_rel_eq) ===> Set_List_rel Set_List_rel_eq) sat_is_un_1 sat_is_un_1_list"
proof -
  let ?R = "Set_List_rel (\<lambda>a b. a = b \<and> fst (fst a) \<noteq> fst (snd a))"
  have [transfer_rule]:
    "(list_all2 (Set_List_rel_eq) ===> list_all2 ?R)
    (map (Set.filter (\<lambda>((a, _), (b, _)). a \<noteq> b))) (map (filter (\<lambda>((a, _), (b, _)). a \<noteq> b)))"
    (is "(_ ===> _ (Set_List_rel ?B)) (_ (Set.filter ?f)) (_ (filter ?f))")
  proof -
    define f where def: "f = ?f"
    have B_eq: "?B = (\<lambda>a b. a = b \<and> f a)" unfolding def by auto
    have aux: "(list_all2 Set_List_rel_eq ===> list_all2 (Set_List_rel ?B))
      (map (Set.filter f)) (map (filter f))"
      unfolding B_eq supply rel_fun_set_filter_list_filter_pred[transfer_rule] by transfer_prover
    then show ?thesis unfolding def by simp
  qed
  have [transfer_rule]: "(?R ===> Set_List_rel Set_List_rel_eq)
      (image (\<lambda>(a, b). {a, b})) (map (\<lambda>(a, b). [a, b]))"
    (is "(Set_List_rel ?A ===> Set_List_rel ?B) (image ?fs) (map ?fl)")
  proof -
    define fs fl where def: "fs = ?fs" "fl = ?fl"
    have [transfer_rule]: "(?A ===> ?B) fs fl"
      unfolding def by (auto simp: rel_set_def dest: rel_funD)
    show ?thesis unfolding def[symmetric] by transfer_prover
  qed
  show ?thesis unfolding sat_is_un_1_eq_sat_is_un_1'_unfold sat_is_un_1_list_def Let_def
    by transfer_prover
qed

subsubsection \<open>List Definition of @{term sat_is_un_2}\<close>

definition
  "sat_is_un_2_list F \<equiv>
    let
      p1 = enumerate 0 F;
      p2 = map (\<lambda>(xsa, xsb). map (\<lambda>x. (x, xsa)) xsb) p1;
      p3 = List.product p2 p2;
      p4 = map (\<lambda>(a, b). List.product a b) p3;
      p5 = concat p4;
      p6 = filter (\<lambda>((a, _), (b, _)). conflict_lit a b) p5;
      p7 = map (\<lambda>(a, b). [a, b]) p6
    in p7"

text \<open>Definition equivalent to @{term sat_is_un_2} and closer to @{term sat_is_un_2_list}.\<close>

definition
  "sat_is_un_2'_prod F \<equiv>
    let
      p1 = enumerate 0 F;
      p2 = map (\<lambda>(xsa, xsb). (\<lambda>x. (x, xsa)) ` xsb) p1;
      p3 = List.product p2 p2;
      p4 = map (\<lambda>(a, b). a \<times> b) p3;
      p5 = \<Union> (set p4);
      p6 = Set.filter (\<lambda>((a, _), (b, _)). conflict_lit a b) p5
    in p6"

definition "sat_is_un_2' F \<equiv> (\<lambda>(a, b). {a, b}) ` sat_is_un_2'_prod F"

lemma sat_is_un_2_eq_sat_is_un_2': "sat_is_un_2 F = sat_is_un_2' F"
  unfolding sat_is_un_2_def sat_is_un_2'_def sat_is_un_2'_prod_def Let_def
  by (fastforce simp: in_set_enumerate_eq)

lemmas sat_is_un_2_eq_sat_is_un_2'_unfold =
  sat_is_un_2_eq_sat_is_un_2'[unfolded sat_is_un_2'_def sat_is_un_2'_prod_def]

text \<open>@{term sat_is_un_2} is related to @{term sat_is_un_2_list}.\<close>

lemma rel_fun_sat_is_un_2_sat_is_un_2_list[transfer_rule]:
  "(list_all2 Set_List_rel_eq ===> Set_List_rel Set_List_rel_eq) sat_is_un_2 sat_is_un_2_list"
proof -
  let ?R = "\<lambda>a b. a = b \<and> conflict_lit (fst (fst a)) (fst (snd a))"
  have b: "?R = (\<lambda>a b. a = b \<and> (\<lambda>((a, _), (b, _)). conflict_lit a b) a)" by auto
  have [transfer_rule]: "(Set_List_rel_eq ===> Set_List_rel ?R)
      (Set.filter (\<lambda>((a, _), (b, _)). conflict_lit a b)) (filter (\<lambda>((a, _), (b, _)). conflict_lit a b))"
    unfolding b supply rel_fun_set_filter_list_filter_pred[transfer_rule] by transfer_prover
  have [transfer_rule]: "(Set_List_rel ?R ===> Set_List_rel Set_List_rel_eq)
    (image (\<lambda>(a, b). {a, b})) (map (\<lambda>(a, b). [a, b]))"
    (is "(Set_List_rel ?A ===> Set_List_rel ?B) (image ?fs) (map ?fl)")
  proof -
    define fs fl where def: "fs = ?fs" "fl = ?fl"
    then have [transfer_rule]: "(?A ===> ?B) fs fl" by (auto simp: rel_set_def dest: rel_funD)
    show ?thesis unfolding def[symmetric] by transfer_prover
  qed
  show ?thesis unfolding sat_is_un_2_eq_sat_is_un_2'_unfold sat_is_un_2_list_def Let_def
    by transfer_prover
qed


subsubsection \<open>List Definition of @{term sat_is}\<close>

definition
  "sat_is_list F \<equiv> if is_n_sat_list 3 F
    then (sat_is_un_1_list F @ sat_is_un_2_list F, length F)
    else ([], 1)"
lemmas sat_is_list_unfold = sat_is_list_def[unfolded sat_is_un_1_list_def sat_is_un_2_list_def]

text \<open>@{term sat_is} is related to @{term sat_is_list}.\<close>

lemma sat_is_list_rel[transfer_rule]:
  "(list_all2 Set_List_rel_eq ===> (rel_prod (Set_List_rel Set_List_rel_eq) (=))) sat_is sat_is_list"
    unfolding sat_is_def sat_is_list_def by transfer_prover

subsection \<open>@{term sat_is_list} is a reduction from @{term three_sat_list} to
@{term independent_set_list}.\<close>

theorem is_reduction_sat_is_list: "is_reduction sat_is_list three_sat_list independent_set_list"
  unfolding three_sat_list_def independent_set_list_def
  using is_reduction_sat_is[unfolded three_sat_eq_Collect_three_sat_pred
    independent_set_eq_Collect_independent_set_pred] rel_fun_three_sat_pred_three_sat_list_pred
  apply (rule transfer_is_reduction_Collect)
  apply (transfer_prover, transfer_prover)
  by (fact list_all2_Set_List_rel_transl_list_list_list_set)

end
