\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Simps_To
  imports View_Utils
begin

paragraph \<open>Summary\<close>
text \<open>A simple framework to ask for the normal form of a term on the user-level.
Example usage see below.\<close>

definition "SIMPS_TO s t \<equiv> s = t"

lemma SIMPS_TO_iff: "SIMPS_TO s t \<longleftrightarrow> s = t" unfolding SIMPS_TO_def by simp

text \<open>Prevent simplification of second argument\<close>
lemma SIMPS_TO_cong [cong]: "s = s' \<Longrightarrow> SIMPS_TO s t = SIMPS_TO s' t" by simp

lemma SIMPS_TOI: "SIMPS_TO s s" unfolding SIMPS_TO_iff by simp

ML_file\<open>simps_to.ML\<close>

subparagraph \<open>Example\<close>

experiment
begin

schematic_goal "((True \<and> False) \<and> False) = ?X"
  apply simp (*?X unsolved*)
  oops

schematic_goal test: "((True \<and> False) \<and> False) = ?X"
  apply (subst SIMPS_TO_iff[symmetric])
  apply (tactic \<open>HEADGOAL (Simps_To.SIMPS_TO_tac (simp_tac @{context}))\<close>)
  (* above tactic call corresponds to the following:
  apply (simp, rule SIMPS_TOI)
  *)
  done  (*?X \<mapsto> False*)

end

end