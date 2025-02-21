\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory States_Base
  imports
    (* Trie.Trie *)
    Main
begin

paragraph \<open>Summary\<close>
text \<open>States are abstractions of functions with updates.\<close>

(*an alternative using tries, which turned out to be too slow because the construction of the trie
cannot be evaluated by normalisation as it is*)
(* datatype ('k, 'v) state = State "('k, 'v) trie \<times> ('k list \<Rightarrow> 'v)"

definition "interp_state s k \<equiv> case_state (\<lambda>(t, s). case lookup_trie t k of None \<Rightarrow> s k | Some v \<Rightarrow> v) s"

definition "state s \<equiv> State (empty_trie, s)"

lemma interp_state_state_eq: "interp_state (state s) = s"
  unfolding interp_state_def state_def by simp

definition "update_state k v \<equiv> case_state (\<lambda>(t, s). State (update_trie k v t, s))"

lemma interp_update_state_eq: "interp_state (update_state k v st) = (interp_state st)(k := v)"
  unfolding update_state_def interp_state_def
  by (cases st) (auto split: prod.splits option.splits simp: lookup_update) *)

datatype ('k, 'v) state = State "('k list \<Rightarrow> 'v)"

definition "interp_state s k \<equiv> case_state (\<lambda>s. s k) s"

definition "state s \<equiv> State s"

lemma interp_state_state_eq: "interp_state (state s) = s"
  unfolding interp_state_def state_def by simp

definition "update_state k v \<equiv> case_state (\<lambda>s. State (s(k := v)))"

lemma interp_update_state_eq: "interp_state (update_state k v st) = (interp_state st)(k := v)"
  unfolding update_state_def interp_state_def
  by (cases st) (auto split: prod.splits option.splits)

end
