\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_Nat_To_IMP_Minus_Base
  imports
    HOL.HOL
    ML_Unification.ML_Tactic_Utils
    ML_Unification.Setup_Result_Commands
    ML_Typeclasses.ML_Typeclasses
begin

paragraph \<open>Summary\<close>
text \<open>Basic setup and general ML utilities.\<close>

setup_result HOL_Nat_To_IMP_Minus_base_logger =
  \<open>Logger.new_logger Logger.root "HOL_Nat_To_IMP_Minus_Base"\<close>

ML_file\<open>hol_nat_to_imp_util.ML\<close>

end
