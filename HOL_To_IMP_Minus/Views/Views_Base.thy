\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Views_Base
  imports "HOL-Library.FuncSet"
begin

paragraph \<open>Summary\<close>
text \<open>Views are abstractions of function restrictions. They consist of a
state and set of keys on which the state is restricted on.\<close>

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

datatype 'k keys = Keys "'k set"

definition "interp_keys \<equiv> case_keys id"

definition "empty_keys \<equiv> Keys {}"

lemma interp_empty_keys_eq [simp]: "interp_keys empty_keys = {}"
  unfolding interp_keys_def empty_keys_def by simp

definition "insert_key k ks \<equiv> case_keys (\<lambda>ks. Keys (insert k ks)) ks"

lemma interp_insert_key_eq [simp]:
  "interp_keys (insert_key k ks) = insert k (interp_keys ks)"
  unfolding insert_key_def interp_keys_def
  by (cases ks) simp

datatype ('k, 'v) view = View "('k, 'v) state" "'k keys"

definition "interp_view \<equiv>
  case_view (\<lambda>st ks. restrict (interp_state st) (interp_keys ks))"

definition "view_state \<equiv> case_view (\<lambda>st _. st)"
definition "view_keys \<equiv> case_view (\<lambda>_ ks. ks)"

lemma interp_view_eq:
  "interp_view v = restrict (interp_state (view_state v)) (interp_keys (view_keys v))"
  unfolding view_state_def view_keys_def interp_view_def interp_state_def
  by (cases v) simp

lemma interp_state_view_eq [simp]:
  "interp_state (view_state (View st ks)) = interp_state st"
  unfolding view_state_def by simp

lemma interp_keys_view_eq [simp]:
  "interp_keys (view_keys (View st ks)) = interp_keys ks"
  unfolding view_keys_def by simp

lemma interp_view_view_eq_interp_view [simp]:
  "interp_view (View (view_state v) (view_keys v)) = interp_view v"
  unfolding interp_view_eq by (cases v) simp

lemma interp_view_app_eq_if_mem_interp_keys [simp]:
  assumes "k \<in> interp_keys (view_keys v)"
  shows "interp_view v k = interp_state (view_state v) k"
  using assms unfolding interp_view_eq by simp

lemma interp_view_app_eq_if_not_mem_interp_keys [simp]:
  assumes "k \<notin> interp_keys (view_keys v)"
  shows "interp_view v k = undefined"
  using assms unfolding interp_view_eq by simp

definition "empty_view \<equiv> View empty_state empty_keys"

lemma interp_state_empty_view_eq [simp]:
  "interp_state (view_state empty_view) = interp_state empty_state"
  unfolding empty_view_def by simp

lemma interp_keys_empty_view_eq [simp]:
  "interp_keys (view_keys empty_view) = interp_keys empty_keys"
  unfolding empty_view_def by simp

lemma restrict_empty_eq [simp]: "restrict f {} = K_undef"
  by (simp add: restrict_def K_undef_def)

lemma interp_empty_view_eq [simp]: "interp_view empty_view = K_undef"
  unfolding interp_view_eq by simp

definition "update_state_view v k val \<equiv>
  case_view (\<lambda>st ks. View (update_state st k val) ks) v"

lemma interp_state_update_state_view_eq [simp]:
  "interp_state (view_state (update_state_view v k val)) =
    interp_state (update_state (view_state v) k val)"
  unfolding update_state_view_def by (cases v) simp

lemma interp_keys_update_state_view_eq [simp]:
  "interp_keys (view_keys (update_state_view v k val)) = interp_keys (view_keys v)"
  unfolding update_state_view_def by (cases v) simp

lemma interp_update_state_view_eq [simp]:
  "interp_view (update_state_view v k val) =
    interp_view (View (update_state (view_state v) k val) (view_keys v))"
  by (simp add: interp_view_eq)

definition "insert_key_view k \<equiv> case_view (\<lambda>st ks. View st (insert_key k ks))"

lemma interp_state_insert_key_view_eq [simp]:
  "interp_state (view_state (insert_key_view k v)) = interp_state (view_state v)"
  unfolding insert_key_view_def by (cases v) simp

lemma interp_keys_insert_key_view_eq [simp]:
  "interp_keys (view_keys (insert_key_view k v)) = interp_keys (insert_key k (view_keys v))"
  unfolding insert_key_view_def by (cases v) simp

lemma interp_insert_key_view_eq [simp]:
  "interp_view (insert_key_view k v) =
    interp_view (View (view_state v) (insert_key k (view_keys v)))"
  by (simp add: interp_view_eq)

definition "update_view v k val \<equiv> insert_key_view k (update_state_view v k val)"

lemma interp_state_update_view_eq [simp]:
  "interp_state (view_state (update_view v k val)) =
    interp_state (update_state (view_state v) k val)"
  unfolding update_view_def by simp

lemma interp_keys_update_view_eq [simp]:
  "interp_keys (view_keys (update_view v k val)) =
    interp_keys (insert_key k (view_keys v))"
  unfolding update_view_def by simp

lemma restrict_update_eq_restrict_update_insert:
  "(restrict f S)(k := v) = restrict (f(k := v)) (insert k S)"
  by auto

lemma interp_update_view_eq [simp]:
  "interp_view (update_view v k val) = (interp_view v)(k := val)"
  by (simp add: interp_view_eq restrict_update_eq_restrict_update_insert)

lemma interp_view_update_eq_if_interp_view_eq:
  assumes "interp_view v = interp_view v'"
  shows "interp_view (update_view v k val) = interp_view (update_view v' k val)"
  using assms by simp


end