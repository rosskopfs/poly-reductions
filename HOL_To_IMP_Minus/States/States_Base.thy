\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory States_Base
  imports Main
begin

paragraph \<open>Summary\<close>
text \<open>States are abstractions of functions with updates.\<close>

definition "K_undef \<equiv> \<lambda>_. undefined"

datatype ('k, 'v) state = State "'k \<Rightarrow> 'v"

definition "interp_state \<equiv> case_state id"

definition "empty_state \<equiv> State K_undef"

lemma interp_empty_state_eq: "interp_state empty_state = K_undef"
  unfolding interp_state_def empty_state_def K_undef_def by simp

definition "update_state st k v \<equiv> case_state (\<lambda>st. State (st(k := v))) st"

lemma interp_update_state_eq [simp]:
  "interp_state (update_state st k v) = (interp_state st)(k := v)"
  unfolding update_state_def interp_state_def by (cases st) simp

end
