\<^marker>\<open>creator Kevin Kappelmann\<close>
theory Expression_Refinements_Assign_Pure_Assign_Base
  imports
    Expression_Refinements_Assign_Pure_Base
    Expression_Assigns_Base
begin

context
  fixes eval_eb_impure :: "('t :: {one, plus}, 'sv, 'si, 'sv, 'ebi) eval_time"
  and eval_eb_pure :: "('t, 'sv, 'si, 'sv, 'ebp) eval_time"
  and refine_eb :: "('ebp, 'ebi) refine_fn"
  and eval_ea_impure :: "('t, 'sv, 'si, 'sv, 'eai) eval_time"
  and eval_ea_pure :: "('t, 'sv, 'si, 'sv, 'eap) eval_time"
  and refine_ea :: "('eap, 'eai) refine_fn"
  and eval_assign_impure_state eval_assign_pure_state
  defines "eval_assign_impure_state \<equiv> eval_exp_assign_base eval_eb_impure eval_ea_impure"
  and "eval_assign_pure_state \<equiv> eval_exp_assign_base eval_eb_pure eval_ea_pure"
begin

fun refine_assign_pure_exp_assign_base where
  "refine_assign_pure_exp_assign_base (EABase eb) = EABase (refine_eb eb)"
| "refine_assign_pure_exp_assign_base (Assign si ea) = Assign si (refine_ea ea)"

lemma refine_assign_pure_exp_assign_base_correct:
  assumes "refines_assign_pure_fun eval_eb_impure eval_eb_pure refine_eb"
  and "refines_assign_pure_fun eval_ea_impure eval_ea_pure refine_ea"
  shows "refines_assign_pure_fun eval_assign_impure_state eval_assign_pure_state
    refine_assign_pure_exp_assign_base"
proof (intro refines_assign_pure_funI refines_assign_pureI)
  fix e s t sf v
  assume "eval_assign_impure_state (refine_assign_pure_exp_assign_base e) s t sf v"
  then show "\<exists>t' sf'. eval_assign_pure_state e s t' sf' v"
  unfolding eval_assign_impure_state_def
  proof (induction e rule: refine_assign_pure_exp_assign_base.induct)
    case (1 eb)
    then have "eval_eb_impure (refine_eb eb) s t sf v" by auto
    with assms obtain t' sf' where "eval_eb_pure eb s t' sf' v"
      using refines_assign_pure_funE by metis
    then show ?case unfolding eval_assign_pure_state_def by blast
  next
    case (2 si ea)
    thm eval_exp_assign_base_AssignE
    then obtain t' s' where
      "eval_ea_impure (refine_ea ea) s t' s' v" "sf = s'(si := v)" "t = t' + 1" by auto
    with assms obtain t'' sf' where "eval_ea_pure ea s t'' sf' v"
      using refines_assign_pure_funE by metis
    then show ?case unfolding eval_assign_pure_state_def by blast
  qed
qed


end
