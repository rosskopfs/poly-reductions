\<^marker>\<open>creator Fabian Huch\<close>
theory IMP_Base
  imports Eq_On
begin

type_synonym vname = string
type_synonym val = nat
type_synonym state = "vname \<Rightarrow> val"

text "Syntactic sugar to write states:"
definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. 0"
syntax
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"

bundle state_syntax
begin
notation null_state ("<>")
end

section \<open>Important operations\<close>

text \<open>Variables, syntactic substitution, and maximum constant\<close>

class vars =
  fixes vars :: "'a \<Rightarrow> vname list"
begin

lemma vars_finite[intro,simp]: "finite (set (vars x))"
by simp

end

class subst = vars +
  fixes subst :: "(vname \<Rightarrow> vname) \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes subst_vars[simp]: "set (vars (subst m c)) = m ` set (vars c)"

class max_const =
  fixes max_const :: "'a \<Rightarrow> nat"

definition max_state :: "vname list \<Rightarrow> state \<Rightarrow> nat" where
  "max_state vrs s \<equiv> foldr (\<lambda>x. max (s x)) vrs 0"

lemma max_state_empty[simp]: "max_state [] s = 0"
  unfolding max_state_def by simp

lemma max_state_cons[simp]: "max_state (x#xs) s = max (s x) (max_state xs s)"
  unfolding max_state_def by simp

lemma max_state_concat[simp]: "max_state (as @ bs) s = max (max_state as s) (max_state bs s)"
  by (induction as) (auto simp: max_state_def)

lemma max_state_upd[simp]: "max_state xs (s(x := y)) \<le> max y (max_state xs s)"
  by (induction xs) auto

lemma max_state_nonintf[simp]: "x \<notin> set xs \<Longrightarrow> max_state xs (s(x := y)) = max_state xs s"
  by (induction xs) auto

lemma max_state_part[simp,intro]: "s = s' on set vs \<Longrightarrow> max_state vs s = max_state vs s'"
  unfolding max_state_def by (induction vs) (auto simp: eq_on_def)


definition max_exp :: "'a::{max_const,vars} \<Rightarrow> state \<Rightarrow> nat" where
  "max_exp e s = max (max_const e) (max_state (vars e) s)"


fun num_bits :: "nat \<Rightarrow> nat" where
"num_bits 0 = 0" |
"num_bits n = Suc (num_bits (n div 2))"

lemma num_bits_double[simp]: "num_bits (n + n) \<le> Suc (num_bits n)"
  by (induction n rule: num_bits.induct) auto

end