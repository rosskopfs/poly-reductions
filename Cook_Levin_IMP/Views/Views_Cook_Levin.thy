\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Views_Cook_Levin
  imports
    IMP_Minus.Call_By_Prefixes
    IMP_Minus.AExp
    IMP_Minus.Big_StepT
    Simps_To
    Views_Base
    ML_State_Seq
begin

paragraph \<open>Summary\<close>
text \<open>Views adapted to track @{session IMP_Minus} state changes in the
@{session Cook_Levin_IMP} refinement theorems.\<close>

text\<open>The next lemmas are needed since, in the Cook-Levin project,
the correctness theorems for the refinements state their state changes in terms
of functions (i.e. the semantics of states) directly.

In principle, we may not require being able to inject a @{type state} into a @{term State}.\<close>

lemma interp_state_State_eq:
  "interp_state (State s) = s"
  unfolding interp_state_def by simp

lemma interp_keys_Keys_eq:
  "interp_keys (Keys ks) = ks"
  unfolding interp_keys_def by simp


text \<open>We now set up the framework that tracks state changes of IMP commands
by using a @{typ "(vname, val) view"}. More precisely, we will keep track of
an view equality that relates the initial state of an IMP program to its current
state.

This tracking happens in a special premise, which we set up next.\<close>

definition "VIEW (v :: AExp.state) \<equiv> v"

text \<open>@{term VIEW} is just a wrapper that contains a state.\<close>

lemma VIEW_eq: "VIEW v = v" unfolding VIEW_def by simp

text \<open>Prevent simplification of arguments\<close>
lemma VIEW_cong [cong]: "VIEW v = VIEW v" by simp

text \<open>In the beginning, we simply know that the view is equal to itself.\<close>

lemma VIEW_start: "VIEW (interp_view v) = VIEW (interp_view v)" by simp

text \<open>The following is used to rewrite state retrievals according to a tracked
view equality.\<close>

lemma view_state_app_eqI:
  assumes "interp_view v = interp_view v'"
  and "interp_state (view_state v) = s"
  and "k \<in> interp_keys (view_keys v)"
  and "interp_view v' k = val"
  shows "s k = val"
  apply (subst assms(2)[symmetric])
  apply (subst assms(4)[symmetric])
  apply (subst assms(1)[symmetric])
  by (simp add: interp_view_eq assms(3))

lemma VIEW_state_app_eqI:
  assumes "VIEW (interp_view v) = VIEW (interp_view v')"
  and  "SIMPS_TO (interp_state (view_state v)) s"
  and "k \<in> interp_keys (view_keys v)"
  and "SIMPS_TO (interp_view v' k) val"
  shows "s k = val"
  using assms unfolding VIEW_eq SIMPS_TO_iff
  by (fact view_state_app_eqI)

text \<open>The following is used to update a view equality according to a new
retrieval condition.\<close>

lemma update_view_state_app_eq:
  assumes "interp_view v = interp_view v'"
  and "interp_state (view_state v) = s"
  and "s k = val"
  and "val = val'"
  shows "interp_view (insert_key_view k v) = interp_view (update_view v' k val')"
  by (simp only: interp_update_view_eq flip: assms(1,4))
  (auto simp: interp_view_eq assms(2,3))

lemma update_VIEW_state_app_eq:
  assumes "VIEW (interp_view v) = VIEW (interp_view v')"
  and  "SIMPS_TO (interp_state (view_state v)) s"
  and "s k = val"
  and "SIMPS_TO val val'"
  shows "VIEW (interp_view (insert_key_view k v)) =
    VIEW (interp_view (update_view v' k val'))"
  using assms unfolding VIEW_eq SIMPS_TO_iff
  by (fact update_view_state_app_eq)

text \<open>The following is used to update a view equality according to a new
update condition.\<close>

lemma update_view_state_eq_update:
  assumes "interp_view v = interp_view v'"
  and "interp_state (view_state v) = s'"
  and "s = s'(k := val)"
  and "val = val'"
  shows "interp_view (View (State s) (insert_key k (view_keys v))) =
    interp_view (update_view v' k val')"
  using assms(2-)
  by (subst interp_view_update_eq_if_interp_view_eq[OF assms(1)[symmetric]])
  (simp add: interp_view_eq interp_state_State_eq)

lemma update_VIEW_state_eq_update:
  assumes "VIEW (interp_view v) = VIEW (interp_view v')"
  and "SIMPS_TO (interp_state (view_state v)) s'"
  and "s = s'(k := val)"
  and "SIMPS_TO val val'"
  shows "VIEW (interp_view (View (State s) (insert_key k (view_keys v)))) =
    VIEW (interp_view (update_view v' k val'))"
  using assms unfolding VIEW_eq SIMPS_TO_iff by (fact update_view_state_eq_update)


text \<open>The following operation is needed because the correctness theorems are
not stated in terms of finite sets but general sets; as a result, the restriction
cannot be expressed in terms of insert operations.\<close>

definition "update_keys_view v ks \<equiv> View (view_state v) ks"

lemma interp_state_update_keys_view_eq [simp]:
  "interp_state (view_state (update_keys_view v ks)) = interp_state (view_state v)"
  unfolding update_keys_view_def by simp

lemma interp_keys_update_keys_view_eq [simp]:
  "interp_keys (view_keys (update_keys_view v ks)) = interp_keys ks"
  unfolding update_keys_view_def by simp

lemma interp_update_keys_view_eq [simp]:
  "interp_view (update_keys_view v ks) = interp_view (View (view_state v) ks)"
  by (simp add: interp_view_eq)

lemma interp_update_keys_view_update_view_eq_if_mem:
  assumes "k \<in> interp_keys ks"
  shows "interp_view (update_keys_view (update_view v k val) ks)
  = interp_view (update_state_view (update_keys_view v ks) k val)"
  using assms by (simp add: interp_view_eq)

lemma interp_update_keys_view_update_view_eq_if_not_mem:
  assumes "k \<notin> interp_keys ks"
  shows "interp_view (update_keys_view (update_view v k val) ks)
  = interp_view (update_keys_view v ks)"
  using assms by (simp add: interp_view_eq)

text \<open>The following is used to update a view equality according to a set of
equality conditions, as obtained, for example, when invoking a subprogram.

Note: the orders of @{term s} and @{term s'} are not in a canonical order in
the following theorem because all IMP correctness theorems are stated that way,
i.e.  they once put @{term s} on the left-hand side and once on the right-hand side.\<close>

lemma update_view_invoke_subprogram_vars:
  assumes "interp_view v = interp_view v'"
  and "interp_state (view_state v) = s"
  and "\<forall>var \<in> vars. s (add_prefix p var) = s' (add_prefix p var)"
  and "\<And>var. var \<in> vars \<Longrightarrow> add_prefix p var \<in> interp_keys (view_keys v)"
  and "\<And>var. var \<in> vars \<Longrightarrow> add_prefix p var \<in> interp_keys (view_keys v')"
  shows "interp_view (View (State s') (Keys (add_prefix p ` vars)))
    = interp_view (update_keys_view v' (Keys (add_prefix p ` vars)))"
proof -
  {
    let ?pvars = "add_prefix p ` vars"
    fix k
    have "restrict s' ?pvars k = restrict (interp_state (view_state v')) ?pvars k"
    proof (cases "k \<in> ?pvars")
      case True
      then obtain var where k_props: "k = add_prefix p var" "var \<in> vars" by blast
      with assms(4,5) have k_mem: "k \<in> interp_keys (view_keys v) \<inter> interp_keys (view_keys v')"
        by blast
      with k_props assms(2,3) have "restrict s' ?pvars k = interp_view v k" by simp
      also from assms(1) k_mem k_props have
        " ... = restrict (interp_state (view_state v')) ?pvars k" by simp
      finally show ?thesis .
    qed simp
  }
  then show ?thesis by (auto simp: interp_view_eq interp_state_State_eq interp_keys_Keys_eq)
qed

lemma update_VIEW_invoke_subprogram_vars:
  assumes "VIEW (interp_view v) = VIEW (interp_view v')"
  and  "SIMPS_TO (interp_state (view_state v)) s"
  and "\<forall>var \<in> vars. s (add_prefix p var) = s' (add_prefix p var)"
  and "\<And>var. var \<in> vars \<Longrightarrow> add_prefix p var \<in> interp_keys (view_keys v)"
  and "\<And>var. var \<in> vars \<Longrightarrow> add_prefix p var \<in> interp_keys (view_keys v')"
  shows "VIEW (interp_view (View (State s') (Keys (add_prefix p ` vars))))
    = VIEW (interp_view (update_keys_view v' (Keys (add_prefix p ` vars))))"
  using assms unfolding VIEW_eq SIMPS_TO_iff by (fact update_view_invoke_subprogram_vars)

ML_file\<open>view_cook_levin.ML\<close>

(*TODO: the framework currently only collects a big view equality without
simplifying it. As a result, every retrieval from these views needs to simplify
a (complex) series of insertions, restrictions, key update operations, etc.
We could instead simplify the views themselves to speed up the proofs and
make them more reliable. Currently, we rely on @{method fastforce} to simplify
the chain of operations.*)

end