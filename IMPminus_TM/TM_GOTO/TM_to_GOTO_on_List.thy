theory TM_to_GOTO_on_List
  imports TM_to_GOTO_on_List_transform
begin

definition goto_prog_state_same_to_TM_config :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> state\<^sub>l \<Rightarrow> config \<Rightarrow> bool" where
  "goto_prog_state_same_to_TM_config K T MAX_POS s cfg \<equiv> TM_to_GOTO_on_List.configuration_of_prog_same_to_TM K T MAX_POS s cfg"

definition TM_to_goto_prog :: "nat \<Rightarrow> nat \<Rightarrow> machine \<Rightarrow> GOTO\<^sub>l_prog" where
  "TM_to_goto_prog K G m = TM_to_GOTO_on_List.GOTO_on_List_Prog m K G"

lemma TM_to_GOTO\<^sub>l_prog_aux:
  "\<And>m tps MAX_POS t tps'.
   turing_machine K G m \<Longrightarrow>
   length tps = K \<and>
   (\<forall>k<K. \<forall>p. (tps ::: k) p < G) \<and> (\<forall>k<K. tps :#: k < MAX_POS) \<Longrightarrow>
   transforms m tps t tps' \<Longrightarrow>
   \<exists>t' s s'.
     t' \<le> (length m * G ^ K + 2 * K + 5) * t + 1 \<and>
     goto_prog_state_same_to_TM_config K t MAX_POS s (0, tps) \<and>
     goto_prog_state_same_to_TM_config K t MAX_POS s' (length m, tps') \<and>
     TM_to_goto_prog K G m \<turnstile>\<^sub>l (pc_start, s) \<rightarrow>\<^bsub>t'\<^esub> (pc_halt, s')"
proof (goal_cases)
  case (1 m tps MAX_POS t tps')
  interpret temp: TM_to_GOTO_on_List m K G tps t tps' MAX_POS
    by (unfold_locales) (simp add: 1)+
  from temp.TM_to_GOTO_on_List_correct_and_in_polynomial_time
  obtain s s' t'
    where t': "t' \<le> (temp.Q * G ^ K + 2 * K + 5) * t + 1"
    and s_to_s': "temp.GOTO_on_List_Prog \<turnstile>\<^sub>l (pc_start, s) \<rightarrow>\<^bsub>t'\<^esub> (pc_halt, s')"
    and s_tps: "temp.configuration_of_prog_same_to_TM s (0, tps)"
    and s'_tps': "temp.configuration_of_prog_same_to_TM s' (temp.Q, tps')"
      by blast
    from t' have t'_goal: "t' \<le> (length m * G ^ K + 2 * K + 5) * t + 1" by simp
    from s_to_s' have s_to_s'_goal: "TM_to_goto_prog K G m \<turnstile>\<^sub>l (pc_start, s) \<rightarrow>\<^bsub>t'\<^esub> (pc_halt, s')"
      by (simp add: TM_to_goto_prog_def)
    from s_tps have s_tps_goal: "goto_prog_state_same_to_TM_config K t MAX_POS s (0, tps)"
      by (simp add: goto_prog_state_same_to_TM_config_def)
    from s'_tps' have s'_tps'_goal: "goto_prog_state_same_to_TM_config K t MAX_POS s' (length m, tps')"
      by (simp add: goto_prog_state_same_to_TM_config_def)
    from t'_goal s_to_s'_goal s_tps_goal s'_tps'_goal
    show ?case by blast
qed

theorem TM_to_GOTO\<^sub>l_prog:
  "\<forall>m::machine. turing_machine K G m \<longrightarrow>
   (\<exists>MAX_POS::nat.
   (\<forall>tps::tape list. length tps = K \<and> (\<forall>k < K. \<forall>p. (tps:::k) p < G) \<and> (\<forall>k < K. tps:#:k < MAX_POS) \<longrightarrow>
   (\<exists>t tps'. transforms m tps t tps' \<longrightarrow>
   (\<exists>t' s s'.
    t' \<le> ((length m) * G ^ K + 2 * K + 5) * t + 1 \<and>
    goto_prog_state_same_to_TM_config K t MAX_POS s (0, tps) \<and>
    goto_prog_state_same_to_TM_config K t MAX_POS s' (length m, tps') \<and>
    TM_to_goto_prog K G m \<turnstile>\<^sub>l (pc_start, s) \<rightarrow>\<^bsub>t'\<^esub> (pc_halt, s')))))"
  using TM_to_GOTO\<^sub>l_prog_aux by (metis (mono_tags))
  
end