theory SAT_Definition
  imports Main
begin

subsection \<open>Definition of SAT\<close>

datatype 'a lit = Pos 'a | Neg 'a

(* TODO: rename, this is not three_sat ! *)
type_synonym 'a three_sat = "'a lit set list"

definition lift :: "('a \<Rightarrow> bool) \<Rightarrow> 'a lit \<Rightarrow> bool" ("_\<up>" 60) where
  "lift \<sigma> \<equiv> \<lambda>l. case l of Pos x \<Rightarrow> \<sigma> x | Neg x \<Rightarrow> \<not> \<sigma> x"

definition models :: "('a \<Rightarrow> bool) \<Rightarrow> 'a three_sat \<Rightarrow> bool" (infixl "\<Turnstile>" 55) where
  "\<sigma> \<Turnstile> F \<equiv> \<forall>cls \<in> set F. \<exists>l \<in> cls. (\<sigma>\<up>) l"

definition sat :: "'a three_sat \<Rightarrow> bool" where
  "sat F \<equiv> \<exists>\<sigma>. \<sigma> \<Turnstile> F"

(* this is three cnf sat *)
definition
  "three_cnf_sat \<equiv> {F. sat F \<and> (\<forall>cls \<in> set F. card cls = 3)}"

definition
  "three_cnf_sat_pred F \<equiv> sat F \<and> (\<forall>cls \<in> set F. card cls = 3)"

lemma three_cnf_sat_unfold_pred: "three_cnf_sat = {F. three_cnf_sat_pred F}"
  unfolding three_cnf_sat_def three_cnf_sat_pred_def by (rule refl)

end
