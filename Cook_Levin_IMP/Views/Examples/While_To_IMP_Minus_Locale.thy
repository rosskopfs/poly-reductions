\<^marker>\<open>creator "Maximilian Schäffeler"\<close>
\<^marker>\<open>contributor "Kevin Kappelmann"\<close>
theory While_To_IMP_Minus_Locale
  imports IMP_Minus.Call_By_Prefixes
begin

lemma Seq_E:
  assumes "(c1;; c2, s1) \<Rightarrow>\<^bsup>t\<^esup> s3"
  obtains s2 t' t'' where "(c1, s1) \<Rightarrow>\<^bsup>t'\<^esup> s2" "(c2, s2) \<Rightarrow>\<^bsup>t''\<^esup> s3"
  using assms by blast

locale While_To_IMP_Minus =
  fixes
    cond_var :: string and
    cond_let :: \<open>'s \<Rightarrow> nat\<close> and
    cond_imp :: \<open>Com.com\<close> and
    body_let :: \<open>'s \<Rightarrow> 's\<close> and
    body_imp :: \<open>Com.com \<close> and
    base_let :: \<open>'s \<Rightarrow> 's\<close> and
    base_imp :: \<open>Com.com\<close> and
    imp_to_let_state :: \<open>string \<Rightarrow> (string \<Rightarrow> nat) \<Rightarrow> 's\<close> and
    loop_let :: \<open>'s \<Rightarrow> 's\<close> and
    vars :: \<open>string set\<close>
  assumes
    eq_on_vars[intro]: \<open>\<And>s s' p. (\<And>i. i \<in> vars \<Longrightarrow> s (p @ i) = s' (p @ i)) \<Longrightarrow>
      imp_to_let_state p s = imp_to_let_state p s'\<close> and
    condition_no_var: \<open>cond_var \<notin> vars\<close> and
  
    base_eq: \<open>\<And>s t s' p. (invoke_subprogram p base_imp, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
      imp_to_let_state p s' = base_let (imp_to_let_state p s)\<close> and
  
    body_eq: \<open>\<And>s t s' p. (invoke_subprogram p body_imp, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
      imp_to_let_state p s' = body_let (imp_to_let_state p s)\<close> and
  
    cond_eq: \<open>\<And>s t s' p. (invoke_subprogram p cond_imp, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
      s' (p @ cond_var) = cond_let (imp_to_let_state p s)
      \<and> imp_to_let_state p s' = imp_to_let_state p s\<close> and
  
    loop_let: \<open>\<And>s. loop_let s = (if cond_let s \<noteq> 0 then loop_let (body_let s) else base_let s)\<close> and
    loop_let_induct: \<open>\<And>P s'. (\<And>s. (cond_let s \<noteq> 0 \<Longrightarrow> P (body_let s)) \<Longrightarrow> P s) \<Longrightarrow> P s'\<close>
begin

definition loop_imp where
  "loop_imp \<equiv>
  cond_imp;;
  WHILE cond_var \<noteq>0 DO (
    body_imp;;
    cond_imp
  );;
  base_imp"

lemma imp_minus_correct:
  assumes \<open>(invoke_subprogram p loop_imp, s) \<Rightarrow>\<^bsup>t\<^esup> s'\<close>
  shows \<open>imp_to_let_state p s' = loop_let (imp_to_let_state p s)\<close>
  using assms
proof (induction \<open>imp_to_let_state p s\<close> arbitrary: s s' t rule: loop_let_induct)
  case 1
  then show ?case
    apply(subst loop_let)
    apply(simp only: loop_imp_def prefix_simps)
    apply (erule Seq_E)+
    apply (erule While_tE)
    subgoal
      apply (cases \<open>cond_let (imp_to_let_state p s) = 0\<close>)
      subgoal
        apply auto
        apply (drule base_eq)
          using cond_eq by auto
        subgoal premises p
          using p(6,7) cond_eq[OF p(3)] by auto
        done
      apply (cases \<open>cond_let (imp_to_let_state p s) = 0\<close>)
      subgoal by (simp add: cond_eq)

      apply(erule Seq_E)+
      subgoal premises p
        apply (simp add: p(7))
        using p
        apply (simp only: prefix_simps)
        apply -
      apply dest_com_gen
          apply force
        using condition_no_var
        using cond_eq body_eq eq_on_vars same_append_eq
         apply (smt (verit, best) cond_eq body_eq condition_no_var eq_on_vars same_append_eq)
        by (smt (verit, best) cond_eq body_eq condition_no_var eq_on_vars same_append_eq)
      done
  qed
end

end