\<^marker>\<open>creator "Maximilian Schäffeler"\<close>
\<^marker>\<open>contributor "Kevin Kappelmann"\<close>
theory Let_To_IMP_Minus_Calls_Locale
  imports IMP_Minus.IMP_Calls
begin

unbundle Com.no_com_syntax
unbundle IMP_Calls.com'_syntax

locale Let_To_IMP_Minus_Calls =
  fixes
    cond_var :: string and
    cond_let :: \<open>'s \<Rightarrow> nat\<close> and
    cond_imp :: \<open>IMP_Calls.com'\<close> and
    body_let :: \<open>'s \<Rightarrow> 's\<close> and
    body_imp :: \<open>IMP_Calls.com'\<close> and
    base_let :: \<open>'s \<Rightarrow> 's\<close> and
    base_imp :: \<open>IMP_Calls.com'\<close> and
    imp_to_let_state :: \<open>AExp.state \<Rightarrow> 's\<close> and
    loop_let :: \<open>'s \<Rightarrow> 's\<close>
  assumes
    imp_to_let_state_correct: "\<And>s s'. s = s'
        on (insert cond_var (\<Union> (set ` vars ` {cond_imp, body_imp, base_imp})))
      \<Longrightarrow> imp_to_let_state s = imp_to_let_state s'" and

    cond_eq: \<open>\<And>s t s'. (cond_imp, s) \<Rightarrow>'\<^bsup>t\<^esup> s' \<Longrightarrow>
      s' cond_var = cond_let (imp_to_let_state s)
      \<and> imp_to_let_state s' = imp_to_let_state s\<close> and

    body_eq: \<open>\<And>s t s'. (body_imp, s) \<Rightarrow>'\<^bsup>t\<^esup> s' \<Longrightarrow>
      imp_to_let_state s' = body_let (imp_to_let_state s)\<close> and

    base_eq: \<open>\<And>s t s'. (base_imp, s) \<Rightarrow>'\<^bsup>t\<^esup> s' \<Longrightarrow>
      imp_to_let_state s' = base_let (imp_to_let_state s)\<close> and

    loop_let: \<open>\<And>s. loop_let s = (if cond_let s \<noteq> 0 then loop_let (body_let s) else base_let s)\<close> and
    loop_let_induct: \<open>\<And>P s'. (\<And>s. (cond_let s \<noteq> 0 \<Longrightarrow> P (body_let s)) \<Longrightarrow> P s) \<Longrightarrow> P s'\<close>
begin

definition "cond_IMP_Minus \<equiv> inline cond_imp"

lemmas cond_IMP_Minus_correct = IMP_Calls.inline[of cond_imp]

definition while_IMP_Minus_Calls where
  "while_IMP_Minus_Calls \<equiv>
  cond_imp;;
  WHILE cond_var \<noteq>0 DO (
    body_imp;;
    cond_imp
  );;
  base_imp"

lemma while_IMP_Minus_Calls_correct:
  assumes \<open>(while_IMP_Minus_Calls, s) \<Rightarrow>'\<^bsup>t\<^esup> s'\<close>
  shows \<open>imp_to_let_state s' = loop_let (imp_to_let_state s)\<close>
  using assms
proof (induction \<open>imp_to_let_state s\<close> arbitrary: s s' t rule: loop_let_induct)
  case 1
  then show ?case
    apply(subst loop_let)
    apply (unfold while_IMP_Minus_Calls_def)
    apply (erule Seq'_tE)+
    apply (erule While'_tE)
    subgoal
      apply (cases \<open>cond_let (imp_to_let_state s) = 0\<close>)
      subgoal using base_eq cond_eq by auto
      subgoal using cond_eq by auto
    done
    subgoal
      apply (cases \<open>cond_let (imp_to_let_state s) = 0\<close>)
      subgoal by (simp add: cond_eq)
        apply(erule Seq'_tE)+
        subgoal
          apply (metis Seq' body_eq cond_eq)
        done
      done
    done
  qed

definition "while_IMP_Minus \<equiv> inline while_IMP_Minus_Calls"

definition "while_IMP_Minus_Calls_vars \<equiv>
  insert cond_var (\<Union> (set ` vars ` {cond_imp, body_imp, base_imp}))"

lemma while_IMP_Minus_Calls_vars_eq:
  "while_IMP_Minus_Calls_vars = set (vars while_IMP_Minus_Calls)"
  unfolding while_IMP_Minus_Calls_vars_def while_IMP_Minus_Calls_def by auto

lemma while_IMP_Minus_correct:
  assumes \<open>(while_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s'\<close>
  shows \<open>imp_to_let_state s' = loop_let (imp_to_let_state s)\<close>
  using assms unfolding while_IMP_Minus_def
  apply (elim IMP_Calls.inline)
  apply (drule while_IMP_Minus_Calls_correct)
  apply (subst (asm) imp_to_let_state_correct[of _ s'])
  apply (subst (asm) while_IMP_Minus_Calls_vars_eq[symmetric])
  by (auto simp add: while_IMP_Minus_Calls_vars_def)

end

end
