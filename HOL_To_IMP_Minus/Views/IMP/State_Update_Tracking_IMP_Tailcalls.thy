\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory State_Update_Tracking_IMP_Tailcalls
  imports
    IMP_Minus.IMP_Tailcalls_Dynamic
    State_Update_Tracking
begin

paragraph \<open>Summary\<close>
text \<open>Track @{theory IMP_Minus.IMP_Tailcalls_Dynamic} state changes.\<close>

ML_file\<open>state_update_tracking_imp_tailcalls.ML\<close>

end
