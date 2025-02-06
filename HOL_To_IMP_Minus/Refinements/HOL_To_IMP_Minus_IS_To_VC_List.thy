theory HOL_To_IMP_Minus_IS_To_VC_List
  imports
    HOL_To_IMP_Minus_Lists
    Karp21.IS_To_VC_List
begin

context HOL_To_HOL_Nat
begin

lemmas list_card_eq = list_card_def[folded length_remdups_card_conv, unfolded list_length_eq_length]
function_compile_nat list_card_eq

end

context HOL_Nat_To_IMP_Minus
begin

lemmas list_card_nat_eq = HTHN.list_card_nat_eq_unfolded
compile_nat list_card_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.list_card_nat by cook

end

context HOL_To_HOL_Nat
begin

lemma If_eq_case: "HOL.If = (\<lambda>b x y. (case b of True \<Rightarrow> x | False \<Rightarrow> y))"
  by (intro ext) simp
lemma is_vc_list_eq[unfolded If_eq_case]:
    "is_vc_list x = (if list_card (concat (fst x)) < (snd x) then x else (fst x, list_card (concat (fst x)) - (snd x)))"
  unfolding is_vc_list_def by (auto split: prod.split)
function_compile_nat is_vc_list_eq

end

context HOL_Nat_To_IMP_Minus
begin

lemmas is_vc_list_nat_eq = HTHN.is_vc_list_nat_eq_unfolded[simplified case_prod_nat_def case_bool_nat_def]
compile_nat is_vc_list_nat_eq
HOL_To_IMP_Minus_correct HOL_To_HOL_Nat.is_vc_list_nat by cook

lemma is_vc_list_IMP_Minus_correct:
  assumes "Rel_nat (s ''is_vc_list_nat.args.x'') x"
  shows "terminates_with_res_IMP_Minus
     (tailcall_to_IMP_Minus is_vc_list_nat_IMP_tailcall) s
     ''is_vc_list_nat.ret''
     (natify (is_vc_list x))"
proof -
  have "HTHN.is_vc_list_nat TYPE('a) (s ''is_vc_list_nat.args.x'') = natify (is_vc_list x)"
    using HOL_To_HOL_Nat.is_vc_list_nat_eq_unfolded[OF assms]
      HOL_To_HOL_Nat.Rel_nat_is_vc_list_nat_unfolded[OF assms]
    by (simp add: Rel_nat_iff_eq_natify)
  then show ?thesis
    using is_vc_list_nat_IMP_Minus_correct[of s x, OF assms] by argo
qed

end

end