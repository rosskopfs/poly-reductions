\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_To_IMP_Base
  imports
    HOL.HOL
    ML_Unification.ML_Tactic_Utils
    ML_Unification.Setup_Result_Commands
    SpecCheck.SpecCheck_Show
begin

paragraph \<open>Summary\<close>
text \<open>Basic setup and general ML utilities.\<close>

setup_result HOL_to_IMP_base_logger = \<open>Logger.new_logger Logger.root_logger "HOL_To_IMP_Base"\<close>

ML_file\<open>hol_to_imp_util.ML\<close>

end
