theory TM_to_GOTO_on_List
  imports GOTO_on_List "IMPminus_TM-Def.Global_Defs" Cook_Levin.Basics "List-Index.List_Index"
          List_Extra
begin

locale TM_to_GOTO_on_List =
    fixes M :: machine
      and K :: nat \<comment>\<open>K: number of tapes\<close>
      and G :: nat \<comment>\<open>G: size of tape character set\<close>
  assumes TM: "turing_machine K G M"

    fixes Q :: nat \<comment>\<open>Q: number of states, halting state excluded; also the halting state\<close>
  assumes Q: "Q = length M"

    fixes TPS :: "tape list"  \<comment>\<open>TPS: input tapes\<close>
      and T :: nat            \<comment>\<open>T: runtime\<close>
      and TPS' :: "tape list" \<comment>\<open>TPS': output tapes\<close>
  assumes runtime_M: "transforms M TPS T TPS'"

    fixes MAX_LEN :: nat    \<comment>\<open>maximum length of all tapes during the execution of the TM\<close>
begin

subsection \<open>Helper functions\<close>

fun tape_content_to_list :: "(nat \<Rightarrow> symbol) \<Rightarrow> nat \<Rightarrow> val list" where
  "tape_content_to_list tp 0 = []" |
  "tape_content_to_list tp (Suc n) = (tape_content_to_list tp n) @ [tp n]"

fun config_to_state :: "config \<Rightarrow> state\<^sub>l" where
  "config_to_state (q, tps) (TP n) = tape_content_to_list (tps ::: n) MAX_LEN" |
  "config_to_state (q, tps) ST = [q]" |
  "config_to_state (q, tps) (HP n) = [tps :#: n]" |
  "config_to_state (q, tps) CHS = []"

abbreviation q_chs_enum_list :: "(state \<times> symbol list) list" where
  "q_chs_enum_list \<equiv> List.product [0..<Q] (product_lists (replicate MAX_LEN [0..<G]))"

lemma q_chs_enum_list_distinct: "distinct q_chs_enum_list"
proof -
  have "distinct [0..<G]"
    by simp
  then have "\<forall>xs \<in> set (replicate MAX_LEN [0..<G]). distinct xs"
    by fastforce
  then have "distinct (product_lists (replicate MAX_LEN [0..<G]))"
    using distinct_product_lists by blast
  moreover
  have "distinct [0..<Q]"
    by fastforce
  ultimately
  show ?thesis
    using distinct_product by blast
qed

abbreviation q_chs_num :: nat where "q_chs_num \<equiv> Q * G ^ MAX_LEN"

lemma q_chs_enum_list_length: "length q_chs_enum_list = q_chs_num"
proof -
  have "length [0..<G] = G"
    by simp
  then have "map length (replicate MAX_LEN [0..<G]) = replicate MAX_LEN G"
    by simp
  moreover
  have "fold (*) (replicate MAX_LEN G) 1 = G ^ MAX_LEN"
    using fold_replicate [where ?f = "(*)" and ?n = MAX_LEN and ?x = G]
    using funpow_times_power [where ?x = G and ?f = "\<lambda>x. MAX_LEN"]
    by auto
  moreover
  have "foldr (*) (replicate MAX_LEN G) 1 = fold (*) (replicate MAX_LEN G) 1"
    by force
  ultimately
  show ?thesis
    using length_product_lists [of "replicate MAX_LEN [0..<G]"]
    by simp
qed

abbreviation s\<^sub>0 :: state\<^sub>l where "s\<^sub>0 \<equiv> config_to_state (0, TPS)"

subsection \<open>Definition of the transform function\<close>

abbreviation entrance_block_len :: nat where
  "entrance_block_len \<equiv> Suc (Suc q_chs_num)"
abbreviation block_for_q_chs_len :: nat where
  "block_for_q_chs_len \<equiv> Suc (3 * K)"

fun label_of_block_for_q_chs :: "state \<times> symbol list \<Rightarrow> label" where
  "label_of_block_for_q_chs (q, chs) =
   Suc entrance_block_len + block_for_q_chs_len * (index q_chs_enum_list (q, chs))"

abbreviation entrance_block :: "GOTO\<^sub>l_prog" where
  "entrance_block \<equiv> [
     IF ST = L [Q] THEN GOTO\<^sub>l pc_halt,
     CHS ::=\<^sub>l ReadChs [0..<K]] @
     map (\<lambda>(q, chs).
       IF ST = L [q] AND CHS = L chs
       THEN GOTO\<^sub>l label_of_block_for_q_chs (q, chs))
     q_chs_enum_list"

lemma entrance_block_length: "length entrance_block = entrance_block_len"
  using q_chs_enum_list_length by fastforce

lemma entrance_block_distinct: "distinct entrance_block"
proof -
  let ?f = "\<lambda>(q, chs).
    IF ST = L [q] AND CHS = L chs THEN GOTO\<^sub>l label_of_block_for_q_chs (q, chs)"
  have "\<forall>q_chs \<in> set q_chs_enum_list. \<forall>q_chs' \<in> set q_chs_enum_list.
        ?f q_chs = ?f q_chs' \<longrightarrow> q_chs = q_chs'"
    by fast
  then have "inj_on ?f (set q_chs_enum_list)"
    using inj_on_def by fast
  with q_chs_enum_list_distinct have "distinct (map ?f q_chs_enum_list)"
    using distinct_map by blast
  then show "distinct entrance_block"
    by fastforce
qed

lemma q_chs_in_entrance_block_iff:
  "(q, chs) \<in> set q_chs_enum_list \<longleftrightarrow>
   (IF ST = L [q] AND CHS = L chs THEN GOTO\<^sub>l label_of_block_for_q_chs (q, chs))
    \<in> set (entrance_block)"
proof
  let ?f = "\<lambda>(q, chs).
    IF ST = L [q] AND CHS = L chs THEN GOTO\<^sub>l label_of_block_for_q_chs (q, chs)"
  fix q chs assume "(q, chs) \<in> set q_chs_enum_list"
  then have "?f (q, chs) \<in> set (map ?f q_chs_enum_list)" by fastforce
  then show "(IF ST = L [q] AND CHS = L chs THEN GOTO\<^sub>l label_of_block_for_q_chs (q, chs))
             \<in> set entrance_block"
    by force
next
  let ?f = "\<lambda>(q, chs).
    IF ST = L [q] AND CHS = L chs THEN GOTO\<^sub>l label_of_block_for_q_chs (q, chs)"
  fix q chs
  assume "(IF ST = L [q] AND CHS = L chs THEN GOTO\<^sub>l label_of_block_for_q_chs (q, chs))
          \<in> set entrance_block"
  then have "?f (q, chs) \<in> set entrance_block" by fast
  then have "?f (q, chs) \<in> set (map ?f q_chs_enum_list)" by force
  then show "(q, chs) \<in> set q_chs_enum_list" by force
qed

fun block_for_q_chs :: "state \<times> action list \<Rightarrow> GOTO\<^sub>l_prog" where
  "block_for_q_chs q_act_s =
     (ST ::=\<^sub>l L [[*] q_act_s]) # \<comment> \<open>update state\<close>
     (concat (map (\<lambda>n. [
        TapeModify n (q_act_s [.] n), \<comment> \<open>tape modification\<close>
        case q_act_s [~] n of
          Left \<Rightarrow> MoveLeft n | Right \<Rightarrow> MoveRight n | Stay \<Rightarrow> NOP\<^sub>l, \<comment> \<open>head movement\<close>
        GOTO\<^sub>l pc_start])
      [0..<K]))" \<comment> \<open>for each tape\<close>

lemma block_for_q_and_chs_length: "length (block_for_q_chs q_act_s) = block_for_q_chs_len"
proof -
  let ?f = "(\<lambda>n. [
    TapeModify n (q_act_s [.] n), \<comment> \<open>tape modification\<close>
    case q_act_s [~] n of
      Left \<Rightarrow> MoveLeft n | Right \<Rightarrow> MoveRight n | Stay \<Rightarrow> NOP\<^sub>l, \<comment> \<open>head movement\<close>
    GOTO\<^sub>l pc_start])"
  have "length (?f n) = 3" for n by auto
  then have "\<forall>xs \<in> set (map ?f [0..<K]). length xs = 3"
    by simp
  then have "length (concat (map ?f [0..<K])) = 3 * K"
    using length_concat_same_length [where ?xss = "map ?f [0..<K]"]
    by auto
  then show ?thesis by auto
qed

abbreviation blocks_for_actions :: "GOTO\<^sub>l_prog" where
  "blocks_for_actions \<equiv>
   concat (map (\<lambda>(q, chs). block_for_q_chs ((M!q) chs)) q_chs_enum_list)"

lemma blocks_for_actions_length: "length blocks_for_actions = block_for_q_chs_len * q_chs_num"
proof -
  let ?f = "\<lambda>(q, chs). block_for_q_chs ((M!q) chs)"  
  from block_for_q_and_chs_length
  have "\<forall>q_chs \<in> set q_chs_enum_list. length (?f q_chs) = block_for_q_chs_len" by fast
  then have "\<forall>blk \<in> set (map ?f q_chs_enum_list). length blk = block_for_q_chs_len" by simp
  then have "length blocks_for_actions = block_for_q_chs_len * (length q_chs_enum_list)"
    using length_concat_same_length [where ?xss = "map ?f q_chs_enum_list"]
    by fastforce
  then show ?thesis
    using q_chs_enum_list_length by presburger
qed

abbreviation GOTO_on_List_Prog :: "GOTO\<^sub>l_prog" where
  "GOTO_on_List_Prog \<equiv> HALT\<^sub>l # entrance_block @ blocks_for_actions @ [HALT\<^sub>l]"

subsection \<open>Correctness of the transform function\<close>

abbreviation configuration_of_prog_same_to_TM :: "state\<^sub>l \<Rightarrow> config \<Rightarrow> bool" (\<open>_ \<sim> _\<close>)
where
  "s \<sim> cfg \<equiv>
    s ST = [fst cfg] \<and> \<comment>\<open>state\<close>
    (\<forall>k < K. s (HP k) = [cfg <#> k]) \<and> \<comment>\<open>head positions of each tape\<close>
    (\<forall>k < K. \<forall>p < MAX_LEN. (s (TP k)) ! p = (cfg <:> k) p)" \<comment>\<open>tape content\<close>

lemma from_entrance_jumps_to_the_right_label:
  assumes "(q, chs) \<in> set q_chs_enum_list"
      and "q < Q"
      and "s ST = [q]"
      and "s (TMP 0) = chs"
    shows "GOTO_on_List_Prog \<turnstile>\<^sub>l
           (Suc (Suc pc_start), s) \<rightarrow>\<^bsub>Suc (Suc (index q_chs_enum_list q_chs))\<^esub>
           (label_of_block_for_q_chs q_chs, s)"
  using assms
  using q_chs_enum_list_distinct
  sorry

lemma block_for_q_chs_correct:
  assumes "exe M (q, tps) = (q', tps')"
    shows "GOTO_on_List_Prog \<turnstile>\<^sub>l
           (label_of_block_for_q_chs (q, read tps), config_to_state (q, tps))
           \<rightarrow>\<^bsub>block_for_q_chs_len\<^esub>
           (pc_start, config_to_state (q', tps'))"
  sorry

lemma TM_to_GOTO_on_List_correct_for_single_step:
  assumes "exe M (q, tps) = (q', tps')"
    shows "GOTO_on_List_Prog \<turnstile>\<^sub>l
           (pc_start, config_to_state (q, tps))
           \<rightarrow>\<^bsub>Suc (Suc (index q_chs_enum_list q_chs)) + block_for_q_chs_len\<^esub>
           (pc_start, config_to_state (q', tps'))"
  sorry

lemma prog_correctly_ends:
  "GOTO_on_List_Prog \<turnstile>\<^sub>l
   (pc_start, config_to_state (Q, tps)) \<rightarrow>\<^bsub>1\<^esub> (pc_halt, config_to_state (Q, tps))"
proof -
  have "config_to_state (Q, tps) ST = [Q]"
    by fastforce
  have "iexec\<^sub>l (IF ST = L [Q] THEN GOTO\<^sub>l pc_halt) (pc, config_to_state (Q, tps)) =
        (pc_halt, config_to_state (Q, tps))" for pc
    by simp
  then have "GOTO_on_List_Prog \<turnstile>\<^sub>l
    (pc_start, config_to_state (Q, tps)) \<rightarrow> (pc_halt, config_to_state (Q, tps))"
    by force
  then show ?thesis by auto
qed

theorem TM_to_GOTO_on_List_correct:
  assumes "GOTO_on_List_Prog \<turnstile>\<^sub>l (pc_start, s\<^sub>0) \<rightarrow>* (pc_halt, s)"
    shows "\<forall>k < K. \<forall>p < MAX_LEN. (s (TP k)) ! p = (TPS':::k) p"
  sorry

subsection \<open>Runtime of the transformed program\<close>

theorem TM_to_GOTO_on_List_in_linear_time:
  "\<exists>c. (GOTO_on_List_Prog \<turnstile>\<^sub>l (pc, s) \<rightarrow>\<^bsub>(c * T)\<^esub> (0, s))"
  sorry

end

end