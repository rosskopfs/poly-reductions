\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Let_To_IMP_Minus_Calls_Tactics
  imports
    States_Cook_Levin_IMP_Minus_Calls
    IMP_Minus.Call_By_Prefixes
begin

unbundle Com.no_com_syntax
unbundle IMP_Calls.com'_syntax

lemma Seq'_assoc:
  "((IMP_Calls.Seq' p1 (IMP_Calls.Seq' p2 p3), s) \<Rightarrow>'\<^bsup>t\<^esup> s')
    \<longleftrightarrow> ((IMP_Calls.Seq' (IMP_Calls.Seq' p1 p2) p3, s) \<Rightarrow>'\<^bsup>t\<^esup> s')"
  by auto

lemma Assign'D: "(x ::= a, s) \<Rightarrow>'\<^bsup>t\<^esup> s' \<Longrightarrow> t = 2 \<and> s' = s(x := aval a s)"
  by auto

lemma atomExp_add_prefix_empty_eq [simp]: "atomExp_add_prefix '''' e = e"
  by (induction e) auto

lemma aexp_add_prefix_empty_eq [simp]: "aexp_add_prefix '''' e = e"
  by (induction e) auto

lemma com_add_prefix_empty_eq [simp]: "com_add_prefix '''' p = p"
  by (induction p) auto

ML_file \<open>let_to_imp_minus_calls_tactics.ML\<close>

end
