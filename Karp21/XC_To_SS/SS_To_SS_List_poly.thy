theory SS_To_SS_List_poly
  imports SS_To_SS_List XC_To_SS_aux

begin

section "the reduction from subset sum to subset sum indeces is polynomial"

subsection "definitions"

definition "mop_check_finiteness \<equiv> \<lambda>(S, w, B). SPECT [finite S \<mapsto> 1]"
definition "mop_mapping_of_set \<equiv> \<lambda>(S, _, _). SPEC (\<lambda>S'. S' = (generate_func S) ` S) (\<lambda>_. 3 * card S + 3 * card S + 1)"
definition "mop_updating_the_weighting \<equiv> \<lambda>(S, w, _). SPEC (\<lambda>w'. w' = (\<lambda>x. w (inv_into S (generate_func S) x))) (\<lambda>_. 3 * card S + 3 * card S + 1)"

definition "ss_to_ss_indeces_alg \<equiv> \<lambda>(S, w, B).
  do {
    b \<leftarrow> mop_check_finiteness (S, w, B);
    if b 
    then do {
      S' \<leftarrow> mop_mapping_of_set (S, w, B);
      w' \<leftarrow> mop_updating_the_weighting (S, w, B);
      RETURNT (S', w', B)
    } 
    else do {
      RETURNT ({}, id, 1)
    }
  }"

definition "ss_to_ss_indeces_space n = 1 + n + n + 1"
definition "ss_to_ss_indeces_time n = 1 + (3 * n + 3 * n + 1) + (3 * n + 3 * n + 1) + 1"

subsection "proof"

lemma ss_to_ss_indeces_size:
"size_ss_indeces (ss_to_ss_indeces (S, w, B)) \<le> ss_to_ss_indeces_space (size_SS (S, w, B))"
by (simp add: size_ss_indeces_def ss_to_ss_indeces_def 
  ss_to_ss_indeces_space_def size_SS_def card_image_le trans_le_add2)

lemma ss_to_ss_indeces_refines:
"ss_to_ss_indeces_alg (S, w, B) \<le> SPEC (\<lambda>y. y = ss_to_ss_indeces (S, w, B)) (\<lambda>_. ss_to_ss_indeces_time (size_SS (S, w, B)))"
unfolding SPEC_def
unfolding ss_to_ss_indeces_alg_def ss_to_ss_indeces_def mop_check_finiteness_def
  mop_mapping_of_set_def mop_updating_the_weighting_def
apply (rule T_specifies_I)
apply (vcg' \<open>-\<close> rules: T_SPEC)
by (auto simp add:ss_to_ss_indeces_time_def size_SS_def one_enat_def Let_def)

theorem ss_to_ss_indeces_is_polyred:
  "ispolyred ss_to_ss_indeces_alg subset_sum subset_sum_indeces size_SS size_ss_indeces"
unfolding ispolyred_def
  apply(rule exI[where x=ss_to_ss_indeces])
  apply(rule exI[where x=ss_to_ss_indeces_time])
  apply(rule exI[where x=ss_to_ss_indeces_space])
  apply safe 
  subgoal 
    using ss_to_ss_indeces_refines 
    by blast
  subgoal
    using ss_to_ss_indeces_size
    by blast 
  subgoal 
    unfolding poly_def ss_to_ss_indeces_time_def
    apply(intro exI[where x=2]) 
    by auto
  subgoal 
    unfolding poly_def ss_to_ss_indeces_space_def
    apply(intro exI[where x=2]) 
    by auto
  subgoal
    using is_reduction_ss_to_ss_indeces
    by blast 
  done 

section "the reduction from subset sum indeces to subset sum list is polynomial"

subsection "definition"

definition "mop_check_finiteness_set \<equiv> \<lambda>(S, _, _). SPECT [finite S \<and> S = {1..card S} \<mapsto> 1]"
definition "mop_mapping_to_list \<equiv>  \<lambda>(S, w, _). SPEC (\<lambda>as. as = map w (sorted_list_of_set S)) (\<lambda>_. 3 * card S + 3 * card S)"
definition "mop_nat_to_int \<equiv> \<lambda>B. SPEC (\<lambda>B'. B' = B) (\<lambda>_. 1)"

definition "ss_indeces_to_ss_list_alg \<equiv> \<lambda>(S, w, B).
  do {
    b \<leftarrow> mop_check_finiteness_set (S, w, B);
    if b
    then do {
      as \<leftarrow> mop_mapping_to_list (S, w, B);
      s \<leftarrow> mop_nat_to_int B;
      RETURNT (as, s)
    }
    else do {
      RETURNT ([], 1)
    }
  }"

definition "ss_indeces_to_ss_list_space n = 1 + 2 * n"
definition "ss_indeces_to_ss_list_time n = 1 + 3 * n + 3 * n + 1"

subsection "proof"

lemma ss_indeces_to_ss_list_size:
"size_ss_list (ss_indeces_to_ss_list (S, w, B)) \<le> ss_indeces_to_ss_list_space (size_ss_indeces (S, w, B))"
by (simp add: size_ss_list_def ss_indeces_to_ss_list_def ss_indeces_to_ss_list_space_def size_ss_indeces_def)

lemma ss_indeces_to_ss_list_refines:
"ss_indeces_to_ss_list_alg (S, w, B) \<le> SPEC (\<lambda>y. y = ss_indeces_to_ss_list (S, w, B)) (\<lambda>_. ss_indeces_to_ss_list_time (size_ss_indeces (S, w, B)))"
unfolding SPEC_def 
unfolding ss_indeces_to_ss_list_alg_def ss_indeces_to_ss_list_def 
mop_check_finiteness_set_def mop_mapping_to_list_def  mop_nat_to_int_def
apply(rule T_specifies_I)
apply(vcg' \<open>-\<close> rules: T_SPEC )
by (auto simp add: ss_indeces_to_ss_list_time_def size_ss_indeces_def one_enat_def Let_def)

theorem ss_indeces_to_ss_list_is_polyred:
  "ispolyred ss_indeces_to_ss_list_alg subset_sum_indeces subset_sum_list size_ss_indeces size_ss_list"
unfolding ispolyred_def
  apply(rule exI[where x=ss_indeces_to_ss_list])
  apply(rule exI[where x=ss_indeces_to_ss_list_time])
  apply(rule exI[where x=ss_indeces_to_ss_list_space])
  apply safe 
  subgoal 
    using ss_indeces_to_ss_list_refines
    by blast
  subgoal
    using ss_indeces_to_ss_list_size
    by blast 
  subgoal 
    unfolding poly_def ss_indeces_to_ss_list_time_def 
    apply(intro exI[where x=2])
    by auto
  subgoal 
    unfolding poly_def ss_indeces_to_ss_list_space_def
    apply(intro exI[where x=2])
    by auto
  subgoal
    using is_reduction_ss_indeces_to_ss_list
    by blast 
  done 

end 