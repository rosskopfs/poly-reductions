theory TM_Extra
  imports Cook_Levin.Basics
begin

lemma exe_state_valid [intro]:
  assumes tm: "turing_machine K G M"
      and exe: "exe M cfg = cfg'"
      and "||cfg|| = K"
      and "fst cfg \<le> length M"
    shows "fst cfg' \<le> length M"
proof (cases "fst cfg < length M")
  case True
  with exe have "cfg' = sem (M ! (fst cfg)) cfg"
    using exe_lt_length by blast
  moreover
  from tm \<open>fst cfg < length M\<close>
  have "turing_command K (length M) G (M ! (fst cfg))"
    using turing_machineD(3) by blast
  moreover
  from \<open>||cfg|| = K\<close> have "length (config_read cfg) = K"
    by (simp add: read_length)
  ultimately
  show ?thesis
    by (simp add: sem_fst turing_commandD(4))
next
  case False
  with exe have "cfg' = cfg"
    using exe_ge_length by auto
  with assms show ?thesis by argo
qed

lemma tape_content_valid [intro]:
  assumes tm: "turing_machine K G M"
      and exe: "exe M cfg = cfg'"
      and "||cfg|| = K"
      and "\<forall>k < K. \<forall>p < MAX_LEN. (cfg <:> k) p < G"
      and "\<forall>k < K. cfg <#> k < MAX_LEN"
      and "k < K"
      and "p < MAX_LEN"
    shows "(cfg' <:> k) p < G"
proof (cases "fst cfg < length M")
  case True
  let ?action = "(M ! fst cfg) (config_read cfg) [!] k"
  let ?old_tape_k = "cfg <!> k"
  let ?new_tape_k_content = "fst (act ?action (cfg <!> k))"

  have "?new_tape_k_content p < G"
  proof (cases "p = snd ?old_tape_k")
    case True
    from assms(3-5) have "config_read cfg ! k < G"
      using read_abbrev \<open>k < K\<close> by auto
    moreover
    from \<open>||cfg|| = K\<close> have "length (config_read cfg) = K"
      by (simp add: read_length)
    moreover
    from tm \<open>fst cfg < length M\<close>
    have "turing_command K (length M) G (M ! (fst cfg))"
      using turing_machineD(3) by blast
    ultimately
    have "fst ?action < G"
      using turing_commandD(2)
      by (metis assms(3-6) tapes_at_read')
    moreover
    have "?new_tape_k_content = (fst ?old_tape_k)(snd ?old_tape_k := fst ?action)"
      by (simp add: act)
    ultimately
    show ?thesis using True by force
  next
    case False
    have "?new_tape_k_content = (fst ?old_tape_k)(snd ?old_tape_k := fst ?action)"
      by (simp add: act)
    with False have "?new_tape_k_content p = (fst ?old_tape_k) p"
      by simp
    then show ?thesis
      using assms by fastforce
  qed
  moreover
  from True exe have cfg'_sem: "cfg' = sem (M ! (fst cfg)) cfg"
    using exe_lt_length by blast
  then have "cfg' <:> k = ?new_tape_k_content"
    by (metis True assms(3) assms(6) prod.collapse sem_snd_tm tm)
  ultimately
  show ?thesis by argo
next
  case False
  with exe have "cfg' = cfg"
    using exe_ge_length by auto
  with assms show ?thesis by presburger
qed

end