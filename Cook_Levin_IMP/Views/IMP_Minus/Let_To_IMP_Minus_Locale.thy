\<^marker>\<open>creator "Maximilian Schäffeler"\<close>
\<^marker>\<open>contributor "Kevin Kappelmann"\<close>
theory Let_To_IMP_Minus_Locale
  imports IMP_Minus.Call_By_Prefixes
begin

locale Let_To_IMP_Minus =
  fixes
    cond_var :: string and
    cond_let :: \<open>'s \<Rightarrow> nat\<close> and
    cond_imp :: \<open>Com.com\<close> and
    body_let :: \<open>'s \<Rightarrow> 's\<close> and
    body_imp :: \<open>Com.com\<close> and
    base_let :: \<open>'s \<Rightarrow> 's\<close> and
    base_imp :: \<open>Com.com\<close> and
    imp_to_let_state :: \<open>string \<Rightarrow> AExp.state \<Rightarrow> 's\<close> and
    loop_let :: \<open>'s \<Rightarrow> 's\<close> and
    vars :: \<open>string set\<close>
  assumes
    eq_on_vars[intro]: \<open>\<And>s s' p. (\<And>i. i \<in> vars \<Longrightarrow> s (add_prefix p i) = s' (add_prefix p i)) \<Longrightarrow>
      imp_to_let_state p s = imp_to_let_state p s'\<close> and
    condition_no_var: \<open>cond_var \<notin> vars\<close> and

    base_eq: \<open>\<And>s t s' p. (invoke_subprogram p base_imp, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
      imp_to_let_state p s' = base_let (imp_to_let_state p s)\<close> and

    body_eq: \<open>\<And>s t s' p. (invoke_subprogram p body_imp, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
      imp_to_let_state p s' = body_let (imp_to_let_state p s)\<close> and

    cond_eq: \<open>\<And>s t s' p. (invoke_subprogram p cond_imp, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
      s' (add_prefix p cond_var) = cond_let (imp_to_let_state p s)
      \<and> imp_to_let_state p s' = imp_to_let_state p s\<close> and

    loop_let: \<open>\<And>s. loop_let s = (if cond_let s \<noteq> 0 then loop_let (body_let s) else base_let s)\<close> and
    loop_let_induct: \<open>\<And>P s'. (\<And>s. (cond_let s \<noteq> 0 \<Longrightarrow> P (body_let s)) \<Longrightarrow> P s) \<Longrightarrow> P s'\<close>
begin

definition while_imp where
  "while_imp \<equiv>
  cond_imp;;
  WHILE cond_var \<noteq>0 DO (
    body_imp;;
    cond_imp
  );;
  base_imp"

lemma while_imp_correct:
  assumes \<open>(invoke_subprogram p while_imp, s) \<Rightarrow>\<^bsup>t\<^esup> s'\<close>
  shows \<open>imp_to_let_state p s' = loop_let (imp_to_let_state p s)\<close>
  using assms
proof (induction \<open>imp_to_let_state p s\<close> arbitrary: s s' t rule: loop_let_induct)
  case 1
  then show ?case
    apply(subst loop_let)
    apply(simp only: while_imp_def prefix_simps)
    apply (erule Seq_tE)+
    apply (erule While_tE)
    subgoal
      apply (cases \<open>cond_let (imp_to_let_state p s) = 0\<close>)
      subgoal using base_eq cond_eq by auto
      subgoal using cond_eq by auto
    done
    subgoal
      apply (cases \<open>cond_let (imp_to_let_state p s) = 0\<close>)
      subgoal by (simp add: cond_eq)
        apply(erule Seq_tE)+
        subgoal
          apply (simp only: prefix_simps)
          apply (metis Seq body_eq cond_eq)
        done
      done
    done
  qed

end

end
