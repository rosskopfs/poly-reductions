theory HOL_To_IMP_Minus_TSAT_To_IS
  imports
    HOL_To_IMP_Minus_Lists
    (* Karp21.TSAT_To_IS_List *)
begin

context HOL_To_HOL_Nat
begin

declare Rel_nat_destruct_prod[Rel_nat]

definition "map_rpair_acc y \<equiv> map_acc (rpair y)"
lemmas map_rpair_acc_eq = map_acc_eq[of "rpair y" for y, folded map_rpair_acc_def]
function_compile_nat map_rpair_acc_eq

fun case_prod_map_rpair where "case_prod_map_rpair (x, xs) = map (rpair x) xs"

case_of_simps case_prod_map_rpair_eq[unfolded map_eq_map_acc_nil,
  folded map_rpair_acc_def] : case_prod_map_rpair.simps
function_compile_nat case_prod_map_rpair_eq

definition "map_case_prod_map_rpair_acc \<equiv> map_acc case_prod_map_rpair"
lemmas map_case_prod_map_rpair_acc_eq = map_acc_eq[of "case_prod_map_rpair",
  folded map_case_prod_map_rpair_acc_def]
function_compile_nat map_case_prod_map_rpair_acc_eq

end

context HOL_Nat_To_IMP_Minus
begin

lemmas map_rpair_acc_nat_eq = HTHN.map_rpair_acc_nat_eq_unfolded[simplified case_list_nat_def]
compile_nat map_rpair_acc_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.map_rpair_acc_nat
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  by (induction "HTHN.rpair y :: 'b \<Rightarrow> _" _ _ arbitrary: s rule: HOL_To_HOL_Nat.map_acc.induct)
  (tactic \<open>HT.start_run_finish_case_tac HT.get_IMP_def HT.get_imp_minus_correct
    HB.get_HOL_eqs @{context} 1\<close>)+

lemmas case_prod_map_rpair_nat_eq = HTHN.case_prod_map_rpair_nat_eq_unfolded[simplified case_prod_nat_def]
compile_nat case_prod_map_rpair_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.case_prod_map_rpair_nat by (cook mode = induction)

lemmas map_case_prod_map_rpair_acc_nat_eq =
  HTHN.map_case_prod_map_rpair_acc_nat_eq_unfolded[simplified case_list_nat_def]
compile_nat map_case_prod_map_rpair_acc_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.map_case_prod_map_rpair_acc_nat
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  by (induction "HTHN.case_prod_map_rpair :: ('a \<times> 'b list) \<Rightarrow> _" _ _ arbitrary: s
    rule: HOL_To_HOL_Nat.map_acc.induct)
  (tactic \<open>HT.start_run_finish_case_tac HT.get_IMP_def HT.get_imp_minus_correct
    HB.get_HOL_eqs @{context} 1\<close>)+

end

    (* let
      p1 = enumerate 0 F;
      p2 = map (\<lambda>(xsa, xsb). map (\<lambda>x. (x, xsa)) xsb) p1;
      p3 = map (\<lambda>xs. List.product xs xs) p2;
      p4 = map (\<lambda>xs. filter (\<lambda>((a, _), (b, _)). a \<noteq> b) xs) p3;
      p5 = concat p4;
      p6 = map (\<lambda>(a, b). [a, b]) p5
    in p6"
 *)



(*TODO: compiled and verify reduction here + move tairec funds from
Tail_Rec_Funs into corresponding locale *)

(*
subsubsection \<open>tail recursive definition of \<open>sat_is_list\<close>\<close>

text \<open>tail recursive definition of \<open>sat_is_un_1_list\<close>\<close>
definition
  "sat_is_un_1_list_tr F \<equiv>
    let
      p1 = enumerate_tr 0 F;
      p2 = map_tr (\<lambda>(xsa, xsb). map_tr (\<lambda>x. (x, xsa)) xsb) p1;
      p3 = map_tr (\<lambda>xs. product_tr xs xs) p2;
      p4 = map_tr (\<lambda>xs. filter_tr (\<lambda>((a, _), (b, _)). a \<noteq> b) xs) p3;
      p5 = concat_tr p4;
      p6 = map_tr (\<lambda>(a, b).  [a, b]) p5
    in p6"

lemma sat_is_un_1_list_tr_eq: "sat_is_un_1_list_tr = sat_is_un_1_list"
  unfolding sat_is_un_1_list_tr_def sat_is_un_1_list_def tr_simps
  by (rule refl)

text \<open>tail recursive definition of \<open>sat_is_un_2_list\<close>\<close>
definition
  "sat_is_un_2_list_tr F \<equiv>
    let
      p1 = enumerate_tr 0 F;
      p2 = map_tr (\<lambda>(xsa, xsb). map_tr (\<lambda>x. (x, xsa)) xsb) p1;
      p3 = product_tr p2 p2;
      p4 = map_tr (\<lambda>(a, b). product_tr a b) p3;
      p5 = concat_tr p4;
      p6 = filter_tr (\<lambda>((a, _), (b, _)). conflict_lit a b) p5;
      p7 = map_tr (\<lambda>(a, b). [a, b]) p6
    in p7"

lemma sat_is_un_2_list_tr_eq: "sat_is_un_2_list_tr = sat_is_un_2_list"
  unfolding sat_is_un_2_list_tr_def sat_is_un_2_list_def tr_simps
  by (rule refl)

definition
  "sat_is_list_tr F \<equiv> if list_all_tr (\<lambda>xs. length_tr (remdups_tr xs) = 3) F
    then (sat_is_un_1_list_tr F @tr sat_is_un_2_list_tr F, length_tr F)
    else ([], 1)"

lemma sat_is_list_tr_eq: "sat_is_list_tr = sat_is_list"
  unfolding sat_is_list_tr_def sat_is_list_def sat_is_un_1_list_tr_eq sat_is_un_2_list_tr_eq tr_simps
  by (rule refl)

*)

(* subsubsection \<open>Tail recursive definition of \<open>is_vc_list\<close>\<close>

definition
  "is_vc_list_tr \<equiv> \<lambda>(E, k). if k > length_tr (remdups_tr (concat_tr E)) then (E, k) else (E, length_tr (remdups_tr (concat_tr E)) - k)"

lemma is_vc_list_tr_eq: "is_vc_list_tr = is_vc_list"
  unfolding is_vc_list_def is_vc_list_tr_def tr_simps by (rule refl) *)


end