theory SAT_Definition
  imports Main
begin

subsection \<open>Definition of SAT\<close>

datatype 'a lit = Pos 'a | Neg 'a

(* maybe use this instead *)
type_synonym 'a clause = "'a lit set"

(* TODO: rename, this is not three_sat ! *)
type_synonym 'a three_sat = "'a lit set list"


definition lift :: "('a \<Rightarrow> bool) \<Rightarrow> 'a lit \<Rightarrow> bool" ("_\<up>" 60) where
  "lift \<sigma> \<equiv> \<lambda>l. case l of Pos x \<Rightarrow> \<sigma> x | Neg x \<Rightarrow> \<not> \<sigma> x"

definition models :: "('a \<Rightarrow> bool) \<Rightarrow> 'a clause list \<Rightarrow> bool" (infixl "\<Turnstile>" 55) where
  "\<sigma> \<Turnstile> F \<equiv> \<forall>cls \<in> set F. \<exists>l \<in> cls. (\<sigma>\<up>) l"

definition sat :: "'a clause list \<Rightarrow> bool" where
  "sat F \<equiv> \<exists>\<sigma>. \<sigma> \<Turnstile> F"

definition SAT where
  "SAT = {F. sat F \<and> (\<forall>cls \<in> set F. finite cls)}"



(* this is three cnf sat *)
definition
  "three_cnf_sat \<equiv> {F. sat F \<and> (\<forall>cls \<in> set F. card cls = 3)}"

lemma three_cnf_satI:
  assumes "sat F"
          "\<forall>cls \<in> set F. card cls = 3"
        shows "F \<in> three_cnf_sat"
  using assms
  unfolding three_cnf_sat_def 
  by blast

end