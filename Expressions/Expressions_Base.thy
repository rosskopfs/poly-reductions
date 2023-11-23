\<^marker>\<open>creator Kevin Kappelmann\<close>
theory Expressions_Base
  imports Main
begin

type_synonym 'si state_id = 'si
type_synonym 'sv state_val = 'sv
type_synonym ('si, 'sv) state = "'si state_id \<Rightarrow> 'sv state_val"

type_synonym 'r result = "'r"

text\<open>Expressions take a state and return, after some time, an updated state and a result.\<close>
type_synonym ('t, 'r, 'si, 'sv, 'e) eval_time =
  "'e \<Rightarrow> ('si, 'sv) state \<Rightarrow> 't \<Rightarrow> ('si, 'sv) state \<Rightarrow> 'r result \<Rightarrow> bool"

text\<open>Turn an evaluation into a pure evaluation that does not modify the state.\<close>
definition "eval_pure_state eval e s t s' v \<equiv> s = s' \<and> (\<exists>s''. eval e s t s'' v)"

lemma eval_pure_stateI[intro]:
  assumes "s = s'"
  and "eval e s t s'' v"
  shows "eval_pure_state eval e s t s' v"
  using assms unfolding eval_pure_state_def by blast

lemma eval_pure_stateE[elim]:
  assumes "eval_pure_state eval e s t s' v"
  obtains s'' where "s = s'" "eval e s t s'' v"
  using assms unfolding eval_pure_state_def by blast

lemma eval_pure_state_mono[mono]:
  assumes "\<And>e s t s' v. f1 e s t s' v \<longrightarrow> g1 e s t s' v"
  shows "eval_pure_state f1 e s t s' v \<longrightarrow> eval_pure_state g1 e s t s' v"
  using assms by blast

named_theorems exp_smart_constructor_def

end