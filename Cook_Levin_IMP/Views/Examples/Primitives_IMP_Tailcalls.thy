\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Primitives_IMP_Tailcalls
  imports
    Compile_HOL_to_IMP_Minus_Calls
    IMP_Minus_Views.Let_To_IMP_Minus_Calls_Locale
    IMP_Minus_Views.Let_To_IMP_Minus_Calls_Tactics
begin

(* lemma
  includes tcom_syntax no_com'_syntax
  assumes "C \<turnstile> (tCall add_IMP ''add_ret'', s) \<Rightarrow>\<^bsup>t\<^esup> s'"
  shows "s' ''add_ret'' = nat_add (s ''add_x'') (s ''add_y'') (s ''add_z'')"
  using assms unfolding add_IMP_def
  apply(rule tCall_tE)
  apply(erule inline)
  print_statement compile_complete
  apply(erule compile_complete)
  sorry *)

end