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

lemma sem_tape:
  assumes exe: "exe M cfg = cfg'"
      and tm: "turing_machine K G M"
      and "||cfg|| = K"
      and q: "fst cfg < length M"
      and "k < K"
    shows "cfg' <!> k = act ((M ! fst cfg) (config_read cfg) [!] k) (cfg <!> k)"
proof -
  from exe have "||cfg'|| = K"
    using tm exe_num_tapes \<open>||cfg|| = K\<close> by metis
  from exe sem'
  have "snd cfg' = map2 act ([!!] (M ! fst cfg) (config_read cfg)) (snd cfg)"
    using q exe_lt_length by auto
  moreover
  have "length ([!!] (M ! fst cfg) (config_read cfg)) = K"
    by (metis assms(3) q read_length tm turing_commandD(1) turing_machineD(3))
  ultimately
  have "snd cfg' ! k = act (([!!] (M ! fst cfg) (config_read cfg)) ! k) (snd cfg ! k)"
    using \<open>||cfg|| = K\<close> \<open>k < K\<close>
    by simp
  then show ?thesis by blast
qed

lemma head_moves_left:
  assumes exe: "exe M cfg = cfg'"
      and tm: "turing_machine K G M"
      and "||cfg|| = K"
      and q: "fst cfg < length M"
      and "(M ! fst cfg) (config_read cfg) [~] k = Left"
      and "k < K"
    shows "snd cfg' :#: k = snd cfg :#: k - 1"
proof -
  have "snd (act (w, Left) (cfg <!> k)) = snd cfg :#: k - 1" for w
    by simp
  moreover
  obtain w where "(M ! fst cfg) (config_read cfg) [!] k =
                  (w, (M ! fst cfg) (config_read cfg) [~] k)"
    by (meson prod.exhaust_sel)
  moreover
  from assms(5) have "(M ! fst cfg) (config_read cfg) [~] k = Left" by blast
  ultimately
  have "snd (act ((M ! fst cfg) (config_read cfg) [!] k) (cfg <!> k)) = snd cfg :#: k - 1"
    by fastforce
  with sem_tape show ?thesis
    using assms by auto
qed

lemma head_moves_right:
  assumes exe: "exe M cfg = cfg'"
      and tm: "turing_machine K G M"
      and "||cfg|| = K"
      and q: "fst cfg < length M"
      and "(M ! fst cfg) (config_read cfg) [~] k = Right"
      and "k < K"
    shows "snd cfg' :#: k = snd cfg :#: k + 1"
proof -
  have "snd (act (w, Right) (cfg <!> k)) = snd cfg :#: k + 1" for w
    by simp
  moreover
  obtain w where "(M ! fst cfg) (config_read cfg) [!] k =
                  (w, (M ! fst cfg) (config_read cfg) [~] k)"
    by (meson prod.exhaust_sel)
  moreover
  from assms(5) have "(M ! fst cfg) (config_read cfg) [~] k = Right" by blast
  ultimately
  have "snd (act ((M ! fst cfg) (config_read cfg) [!] k) (cfg <!> k)) = snd cfg :#: k + 1"
    by fastforce
  with sem_tape show ?thesis
    using assms by auto
qed

lemma head_stay:
  assumes exe: "exe M cfg = cfg'"
      and tm: "turing_machine K G M"
      and "||cfg|| = K"
      and q: "fst cfg < length M"
      and "(M ! fst cfg) (config_read cfg) [~] k = Stay"
      and "k < K"
    shows "snd cfg' :#: k = snd cfg :#: k"
proof -
  have "snd (act (w, Stay) (cfg <!> k)) = snd cfg :#: k" for w
    by simp
  moreover
  obtain w where "(M ! fst cfg) (config_read cfg) [!] k =
                  (w, (M ! fst cfg) (config_read cfg) [~] k)"
    by (meson prod.exhaust_sel)
  moreover
  from assms(5) have "(M ! fst cfg) (config_read cfg) [~] k = Stay" by blast
  ultimately
  have "snd (act ((M ! fst cfg) (config_read cfg) [!] k) (cfg <!> k)) = snd cfg :#: k"
    by fastforce
  with sem_tape show ?thesis
    using assms by auto
qed

lemma exe_tape_modify:
  assumes exe: "exe M cfg = cfg'"
      and tm: "turing_machine K G M"
      and "||cfg|| = K"
      and q: "fst cfg < length M"
      and "k < K"
    shows "cfg' <:> k = (cfg <:> k)(cfg <#> k := ((M ! (fst cfg)) (config_read cfg)) [.] k)"
proof -
  from exe q have "cfg' = sem (M ! (fst cfg)) cfg"
    by (simp add: exe_lt_length)
  also have "... = (
    let (newstate, actions) = (M ! (fst cfg)) (config_read cfg)
    in (newstate, map (\<lambda>(a, tp). act a tp) (zip actions (snd cfg))))"
    by (simp add: sem_def)
  also have "snd ... = map (\<lambda>(a, tp). act a tp)
    (zip (snd ((M ! (fst cfg)) (config_read cfg))) (snd cfg))"
    by (simp add: case_prod_beta)
  also have "... ! k = act ((snd ((M ! (fst cfg)) (config_read cfg))) ! k) (snd cfg ! k)"
    using assms by (metis calculation sem_tape)
  also have "fst ... = (cfg <:> k)(cfg <#> k := ((M ! (fst cfg)) (config_read cfg)) [.] k)"
    by (simp add: act)
  finally show ?thesis
    by blast
qed

lemma exe_head_position:
  assumes exe: "exe M cfg = cfg'"
      and tm: "turing_machine K G M"
      and "||cfg|| = K"
      and "k < K"
    shows "snd cfg' :#: k \<le> snd cfg :#: k + 1"
  apply (cases "fst cfg < length M")
  apply (cases "(M ! fst cfg) (config_read cfg) [~] k")
  using head_moves_left assms apply simp
  using head_stay assms apply simp
  using head_moves_right assms apply simp
  using exe exe_ge_length apply auto
  done

lemma execute_head_position_bounded_by_running_time:
  assumes execute: "execute M cfg t = cfg'"
      and tm: "turing_machine K G M"
      and "||cfg|| = K"
      and "k < K"
    shows "snd cfg' :#: k \<le> snd cfg :#: k + t"
  using assms
  apply (induction t arbitrary: cfg')
  apply simp
  apply simp
  using exe_head_position execute_num_tapes
  by (smt (verit) add.commute le_trans nat_add_left_cancel_le plus_1_eq_Suc)

lemma exe_gt_running_time:
  assumes "transforms m tps T tps'"
      and "t \<ge> T"
    shows "exe m (execute m (0, tps) t) = (execute m (0, tps) t)"
  using assms
  apply (induction t)
  apply (metis (mono_tags, opaque_lifting) exe_ge_length execute.simps(1) fst_conv
         halting_config_def le_zero_eq transforms_halting_config transforms_running_time)
  by (smt (verit) exe_ge_length execute_after_halting_ge fst_conv halting_config_def
      order.order_iff_strict transforms_halting_config transforms_running_time)
  
end