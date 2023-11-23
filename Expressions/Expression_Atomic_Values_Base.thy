\<^marker>\<open>creator Kevin Kappelmann\<close>
theory Expression_Atomic_Values_Base
  imports Expressions_Base
begin

datatype ('si, 'sv) exp_atomic_val_base = V 'sv | SI 'si

inductive eval_exp_atomic_val_base ::
  "('t :: {zero,one}, 'sv, 'si, 'sv, ('si, 'sv) exp_atomic_val_base) eval_time"
where
  eval_exp_atomic_val_base_V: "eval_exp_atomic_val_base (V v) s 0 s v"
| eval_exp_atomic_val_base_SI: "eval_exp_atomic_val_base (SI si) s 1 s (s si)"

inductive_cases eval_exp_atomic_val_base_VE[elim]: "eval_exp_atomic_val_base (V v) s t s' v'"
inductive_cases eval_exp_atomic_val_base_SIE[elim]: "eval_exp_atomic_val_base (SI si) s t s' v"

lemma eval_exp_atomic_val_base_VI[intro]:
  assumes "s = s'"
  and "v = v'"
  and "t = 0"
  shows "eval_exp_atomic_val_base (V v) s t s' v'"
  using assms eval_exp_atomic_val_base.intros by auto

lemma eval_exp_atomic_val_base_SII[intro]:
  assumes "s = s'"
  and "v' = s si"
  and "t = 1"
  shows "eval_exp_atomic_val_base (SI si) s t s' v'"
  using assms eval_exp_atomic_val_base.intros by auto


end