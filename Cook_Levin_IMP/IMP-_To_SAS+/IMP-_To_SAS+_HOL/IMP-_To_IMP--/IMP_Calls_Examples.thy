theory IMP_Calls_Examples
  imports Primitives_IMP_Minus "../../../IMP-/IMP_Calls"
begin

lemma[simp]: "atomExp_add_prefix [] x2 = x2" by (induction x2) auto
lemma[simp]: "aexp_add_prefix [] x2 = x2" by (induction x2) auto
lemma a[simp]: "invoke_subprogram [] c = c"
  by (induction c) auto
lemmas tl_correct =  tl_IMP_Minus_correct_function[of "[]", simplified prefix_simps com_add_prefix.simps a]


definition "single = Seq' (Call' tl_IMP_Minus tl_ret_str) SKIP'"

lemma single_correct':  "(single, s) \<Rightarrow>'\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' tl_ret_str = tl_ret (tl_imp (tl_imp_to_HOL_state [] s))"
  unfolding single_def
  apply (erule Seq'_tE)
  apply (erule Call'_tE)
  apply (drule tl_correct)
  apply auto
  done

lemma single_correct:  "(inline single, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
   s' tl_ret_str = tl_ret (tl_imp (tl_imp_to_HOL_state [] s))"
  apply (erule inline)
  apply (drule single_correct')
  unfolding tl_imp_to_HOL_state_def
  apply simp unfolding single_def
  apply auto
  done


(* Composition: tl (tl (xs)) *)

definition "composed = Seq' (Seq' (Call' tl_IMP_Minus tl_ret_str) (Assign' tl_xs_str (A (V tl_ret_str)))) (Call' tl_IMP_Minus tl_ret_str)"
lemma composed_correct':  "(composed, s) \<Rightarrow>'\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' tl_ret_str = tl_ret (tl_imp \<lparr>tl_xs = tl_ret (tl_imp (tl_imp_to_HOL_state [] s)), tl_ret = undefined\<rparr>)"
  unfolding composed_def
  apply (erule Seq'_tE | erule Call'_tE | erule Assign'_tE)+
  apply (drule tl_correct)+
  apply (auto simp add: tl_imp_to_HOL_state_def tl_imp.simps tl_state_upd_def)
  done

lemma composed_correct:  "(inline composed, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
   s' tl_ret_str = tl_ret (tl_imp \<lparr>tl_xs = tl_ret (tl_imp (tl_imp_to_HOL_state [] s)), tl_ret = undefined\<rparr>)"
  apply (erule inline)
  apply (drule composed_correct')
  unfolding tl_imp_to_HOL_state_def
  apply simp unfolding composed_def
  apply auto
  done

end