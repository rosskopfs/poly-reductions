\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory While_To_IMP_Minus_Tactics
  imports
    Views_Cook_Levin_IMP_Minus
begin
          
lemma Seq_assoc:
  "((Com.Seq p1 (Com.Seq p2 p3), s) \<Rightarrow>\<^bsup>t\<^esup> s') \<longleftrightarrow> ((Com.Seq (Com.Seq p1 p2) p3, s) \<Rightarrow>\<^bsup>t\<^esup> s')"
  by auto        

ML_file \<open>while_to_imp_minus_tactics.ML\<close>
  
end
