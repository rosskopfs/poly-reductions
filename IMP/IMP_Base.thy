\<^marker>\<open>creator Fabian Huch\<close>
theory IMP_Base
  imports Main
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

class subst = vars +
  fixes subst :: "(vname \<Rightarrow> vname) \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes subst_vars[simp]: "set (vars (subst m c)) = m ` set (vars c)"

class max_const =
  fixes max_const :: "'a \<Rightarrow> nat"

end