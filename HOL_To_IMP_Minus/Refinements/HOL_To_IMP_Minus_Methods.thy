theory HOL_To_IMP_Minus_Methods
  imports
    HOL_To_IMP_Tailcalls_Tactics
    HOL_To_IMP_Minus_Goal_Commands
begin

fun correctness_thm_for t = HOL_To_IMP_Minus_Func_Correct_Thms.get_theorem ctxt t

end
