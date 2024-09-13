theory IMPminus_to_TM_Correctness
  imports "IMP_Minus.Small_StepT" \<comment>\<open>TODO: replace with the newly defined timing function using log instead of constant time for natural number operations\<close>
          Cook_Levin.Arithmetic
          IMPminus_State_TM_Tape_List
begin

lemma IMPminus_to_TM_correct: \<comment>\<open>TODO: Maybe another name would be more suitable, e.g. stating that IMP- is no more effective as TM, or another way round?\<close>
  "\<exists>c p. \<forall>prog. (prog, s) \<rightarrow>\<^bsup>t\<^esup> (SKIP, s') \<longrightarrow> (\<exists>m tps'.
       transforms m
       (IMPminus_state_to_TM_tape_list prog s)
       (c * t ^^ p)
       tps' \<and> tape_list_equiv_IMPminus_state prog tps' s')"
  sorry
\<comment>\<open>TODO: "(prog, s) \<rightarrow>-t- (SKIP, s')" should be replaced with the newly defined semantics with timing\<close>

end