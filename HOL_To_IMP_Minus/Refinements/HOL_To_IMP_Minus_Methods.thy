theory HOL_To_IMP_Minus_Methods
  imports
    HOL_To_IMP_Tailcalls_Tactics
    HOL_To_IMP_Minus_Goal_Commands
begin

method preprocess_HOL_To_IMP_Minus_func_correct =
  (erule tailcall_to_IMP_Minus_correct_if_correct),
  (subst compiled_const_defs, simp),
  (subst compiled_const_defs, simp)

method_setup start_run_finish = \<open>
  let
    datatype option = Pattern of bool | Induction
    val option_parser = Parse.group (fn () => "option") (
      (Parse.reserved "pattern" >> K (Pattern true)) ||
      (Parse.reserved "no_pattern" >> K (Pattern false)) ||
      (Parse.reserved "induction" >> K Induction)
    )
    val default_options = (false, false)
    fun apply_option (Pattern b) (_, induction) = (b, induction)
      | apply_option Induction (pattern, _) = (pattern, true)
    val options_parser =
      (Scan.optional (\<^keyword>\<open>(\<close> |-- Parse.!!! (Parse.list1 option_parser) --| \<^keyword>\<open>)\<close>) [])
      >> (fn opts => fold apply_option opts default_options)
    val parser = options_parser -- Parse.thm
  in
    Scan.lift parser >> (fn ((pattern, induction), fact) => fn ctxt =>
      let
        val def_thms = Attrib.eval_thms ctxt [fact]
        val induction_tac = if induction then H.induction_tac ctxt else K all_tac
        val run_finish_tac =
          if pattern
            then H.start_run_finish_pattern_fun_tac
            else H.start_run_finish_no_pattern_fun_tac
        val compiled_const_defs = Named_Theorems.get ctxt \<^named_theorems>\<open>compiled_const_defs\<close>
        fun correctness_thm_for t =
          HOL_To_IMP_Minus_Func_Correct_Thms.get_theorem ctxt t
        val run_finish_tac' =
          run_finish_tac compiled_const_defs correctness_thm_for def_thms ctxt
      in
        SIMPLE_METHOD' (induction_tac THEN_ALL_NEW run_finish_tac')
      end
    )
  end
\<close>

end