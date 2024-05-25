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
  assumes wf_TPS: "length TPS = K \<and> (\<forall>k < K. \<forall>p < MAX_LEN. (TPS ::: k) p < G) \<and> (\<forall>k < K. (TPS :#: k) < MAX_LEN)"
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
  "q_chs_enum_list \<equiv> List.product [0..<Q] (product_lists (replicate K [0..<G]))"

lemma q_chs_enum_list_distinct: "distinct q_chs_enum_list"
proof -
  have "distinct [0..<G]"
    by simp
  then have "\<forall>xs \<in> set (replicate K [0..<G]). distinct xs"
    by fastforce
  then have "distinct (product_lists (replicate K [0..<G]))"
    using distinct_product_lists by blast
  moreover
  have "distinct [0..<Q]"
    by fastforce
  ultimately
  show ?thesis
    using distinct_product by blast
qed

abbreviation q_chs_num :: nat where "q_chs_num \<equiv> Q * G ^ K"

lemma q_chs_enum_list_length: "length q_chs_enum_list = q_chs_num"
proof -
  have "length [0..<G] = G"
    by simp
  then have "map length (replicate K [0..<G]) = replicate K G"
    by simp
  moreover
  have "fold (*) (replicate K G) 1 = G ^ K"
    using fold_replicate [where ?f = "(*)" and ?n = K and ?x = G]
    using funpow_times_power [where ?x = G and ?f = "\<lambda>x. K"]
    by auto
  moreover
  have "foldr (*) (replicate K G) 1 = fold (*) (replicate K G) 1"
    by force
  ultimately
  show ?thesis
    using length_product_lists [of "replicate K [0..<G]"]
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

abbreviation configuration_of_prog_same_to_TM :: "state\<^sub>l \<Rightarrow> config \<Rightarrow> bool" (\<open>_ \<sim> _\<close> 50) where
  "s \<sim> cfg \<equiv>
    s ST = [fst cfg] \<and> \<comment>\<open>state\<close>
    (\<forall>k < K. s (HP k) = [cfg <#> k]) \<and> \<comment>\<open>head positions of each tape\<close>
    (\<forall>k < K. \<forall>p < MAX_LEN. (s (TP k)) ! p = (cfg <:> k) p)" \<comment>\<open>tape content\<close>

abbreviation wf_cfg :: "config \<Rightarrow> bool" where
  "wf_cfg cfg \<equiv>
    fst cfg \<le> Q \<and> \<comment>\<open>state, = Q means halting state\<close>
    length (snd cfg) = K \<and> \<comment>\<open>number of tapes\<close>
    (\<forall>k < K. \<forall>p < MAX_LEN. (cfg <:> k) p < G) \<and> \<comment>\<open>tape content consists of characters < G only\<close>
    (\<forall>k < K. cfg <#> k < MAX_LEN)" \<comment>\<open>tape head position not exceeding max used length of tape\<close>

lemma wf_cfg_start_cfg: "wf_cfg (0, TPS)"
  using wf_TPS by simp

abbreviation read_chars_correspond_to_cfg :: "state\<^sub>l \<Rightarrow> config \<Rightarrow> bool" where
  "read_chars_correspond_to_cfg s cfg \<equiv> (\<forall>k < K. s CHS ! k = cfg <.> k) \<and> length (s CHS) = K"

lemma tape_content_to_list_length [simp]:
  "length (tape_content_to_list tp len) = len"
  by (induction len) auto

lemma tape_content_to_list_correct[intro]:
  "p < len \<Longrightarrow> tape_content_to_list tp len ! p = tp p"
proof (induction len)
  case 0
  then show ?case by blast
next
  case (Suc len)
  then show ?case
  proof (cases "p = len")
    case True
    then show ?thesis
      by auto (metis nth_append_length tape_content_to_list_length)
  next
    case False
    with Suc show ?thesis
      by (auto simp add: nth_append) 
  qed
qed

lemma config_to_state_correct [simp]: "config_to_state cfg \<sim> cfg"
  using tape_content_to_list_correct
  by (metis config_to_state.simps(1-3) surjective_pairing)

text \<open>Each step in the Turing Machine corresponds to no more than
(entrance_block_len + block_for_q_chs_len) steps in the transformed GOTO_on_List program,
starting from pc = 1, ending also at pc = 1.
This whole round of execution can be divided into 5 parts:
1. read TM state, say q, and store it into the variable ST;
   read chars at head positions, say chs, and storing them into the variable CHS
   (2 steps; pc 1 -> 3)
2. going through the "searching table" of state and chars, until matched
   ("index q_chs_enum_list (q, chs)" < q_chs_num steps; pc 3 -> "index q_chs_enum_list (q, chs) + 2")
3. jump to the label of the block for such q and chs
   (1 step; pc "index q_chs_enum_list (q, chs) + 2" -> "label_of_block_for_q_chs (q, chs)")
4. going through the block for q and chs, updating tape content, head positions and state
   (block_for_q_chs_len steps; pc "label_of_block_for_q_chs (q, chs)" -> "label_of_block_for_q_chs (q, chs) + block_for_q_chs_len")
5. jump to the beginning of the program
   (1 step; pc "label_of_block_for_q_chs (q, chs) + block_for_q_chs_len" -> 1)
Each of these 5 parts are either sequentially executed with no jump, or a single jump.
Below first shows that each of them are correct, then the correctness of the program for each single TM step.\<close>

lemma read_state_and_chars_correct:
  assumes "wf_cfg cfg"
      and "s \<sim> cfg"
      and "fst cfg < Q" \<comment>\<open>not in halting state\<close>
    shows "GOTO_on_List_Prog \<turnstile>\<^sub>l (pc_start, s) \<rightarrow>\<^bsub>2\<^esub> (pc_start + 2, s')"
      and "s' \<sim> cfg"
      and "read_chars_correspond_to_cfg s' cfg"
  sorry

lemma search_for_correct_label_for_q_and_chs:
  assumes "wf_cfg cfg"
      and "s \<sim> cfg"
      and "read_chars_correspond_to_cfg s cfg"
    shows "GOTO_on_List_Prog \<turnstile>\<^sub>l
           (pc_start + 2, s) \<rightarrow>\<^bsub>index q_chs_enum_list (hd (s ST), s CHS)\<^esub>
           (pc_start + 2 + index q_chs_enum_list (hd (s ST), s CHS), s)"
  sorry

lemma jump_to_correct_label:
  assumes "wf_cfg cfg"
      and "s \<sim> cfg"
      and "read_chars_correspond_to_cfg s cfg"
    shows "GOTO_on_List_Prog \<turnstile>\<^sub>l
           (pc_start + 2 + index q_chs_enum_list (hd (s ST), s CHS), s) \<rightarrow>
           (label_of_block_for_q_chs (hd (s ST), s CHS), s)"
  sorry

lemma block_for_q_chs_correct:
  assumes "wf_cfg cfg"
      and "s \<sim> cfg"
      and "read_chars_correspond_to_cfg s cfg"
      and "exe M cfg = cfg'"
    shows "GOTO_on_List_Prog \<turnstile>\<^sub>l
           (label_of_block_for_q_chs (hd (s ST), s CHS), s) \<rightarrow>\<^bsub>block_for_q_chs_len\<^esub>
           (label_of_block_for_q_chs (hd (s ST), s CHS) + block_for_q_chs_len, s')"
      and "s' \<sim> cfg'"
      and "wf_cfg cfg'"
  sorry

lemma jump_back_to_begin:
  "GOTO_on_List_Prog \<turnstile>\<^sub>l
   (label_of_block_for_q_chs (hd (s ST), s CHS) + block_for_q_chs_len, s') \<rightarrow>
   (pc_start, s')"
  sorry

corollary TM_to_GOTO_on_List_correct_for_single_step:
  assumes "wf_cfg cfg"
      and "fst cfg < Q"
      and "exe M cfg = cfg'"
  obtains s
    where "\<exists>t_entrance \<le> entrance_block_len.
           GOTO_on_List_Prog \<turnstile>\<^sub>l
           (pc_start, config_to_state cfg)
           \<rightarrow>\<^bsub>t_entrance + block_for_q_chs_len + 2\<^esub>
           (pc_start, s)"
      and "s \<sim> cfg'"
      and "wf_cfg cfg'"
proof -
  have "config_to_state cfg \<sim> cfg" by simp
  with \<open>wf_cfg cfg\<close> \<open>fst cfg < Q\<close> obtain s\<^sub>1 where read_state_and_chars_correct:
    "GOTO_on_List_Prog \<turnstile>\<^sub>l (pc_start, config_to_state cfg) \<rightarrow>\<^bsub>2\<^esub> (pc_start + 2, s\<^sub>1)"
    and s\<^sub>1: "s\<^sub>1 \<sim> cfg" "read_chars_correspond_to_cfg s\<^sub>1 cfg"
    using read_state_and_chars_correct [where ?s = "config_to_state cfg"] by presburger
  with \<open>wf_cfg cfg\<close> have search_for_correct_label_for_q_and_chs:
    "GOTO_on_List_Prog \<turnstile>\<^sub>l
     (pc_start + 2, s\<^sub>1) \<rightarrow>\<^bsub>index q_chs_enum_list (hd (s\<^sub>1 ST), s\<^sub>1 CHS)\<^esub>
     (pc_start + 2 + index q_chs_enum_list (hd (s\<^sub>1 ST), s\<^sub>1 CHS), s\<^sub>1)"
    using search_for_correct_label_for_q_and_chs by presburger
  from s\<^sub>1 \<open>wf_cfg cfg\<close> have jump_to_correct_label:
    "GOTO_on_List_Prog \<turnstile>\<^sub>l
     (pc_start + 2 + index q_chs_enum_list (hd (s\<^sub>1 ST), s\<^sub>1 CHS), s\<^sub>1) \<rightarrow>
     (label_of_block_for_q_chs (hd (s\<^sub>1 ST), s\<^sub>1 CHS), s\<^sub>1)"
    using jump_to_correct_label by presburger
  from s\<^sub>1 \<open>wf_cfg cfg\<close> \<open>exe M cfg = cfg'\<close> obtain s\<^sub>2 where block_for_q_chs_correct:
    "GOTO_on_List_Prog \<turnstile>\<^sub>l
     (label_of_block_for_q_chs (hd (s\<^sub>1 ST), s\<^sub>1 CHS), s\<^sub>1) \<rightarrow>\<^bsub>block_for_q_chs_len\<^esub>
     (label_of_block_for_q_chs (hd (s\<^sub>1 ST), s\<^sub>1 CHS) + block_for_q_chs_len, s\<^sub>2)"
    and "s\<^sub>2 \<sim> cfg'" and "wf_cfg cfg'"
    using block_for_q_chs_correct [where ?s = s\<^sub>1 and ?cfg = cfg and ?cfg' = cfg']
    by blast
  have jump_back_to_begin:
    "GOTO_on_List_Prog \<turnstile>\<^sub>l
     (label_of_block_for_q_chs (hd (s\<^sub>1 ST), s\<^sub>1 CHS) + block_for_q_chs_len, s\<^sub>2) \<rightarrow>
     (pc_start, s\<^sub>2)"
    using jump_back_to_begin by blast

  from read_state_and_chars_correct search_for_correct_label_for_q_and_chs
  have "GOTO_on_List_Prog \<turnstile>\<^sub>l (pc_start, config_to_state cfg)
        \<rightarrow>\<^bsub>2 + index q_chs_enum_list (hd (s\<^sub>1 ST), s\<^sub>1 CHS)\<^esub>
        (pc_start + 2 + index q_chs_enum_list (hd (s\<^sub>1 ST), s\<^sub>1 CHS), s\<^sub>1)"
    by blast
  moreover
  have "(hd (s\<^sub>1 ST), s\<^sub>1 CHS) \<in> set q_chs_enum_list"
  proof -
    from \<open>s\<^sub>1 \<sim> cfg\<close> \<open>fst cfg < Q\<close> \<open>wf_cfg cfg\<close> have "hd (s\<^sub>1 ST) < Q" by auto
    
    from s\<^sub>1 \<open>s\<^sub>1 \<sim> cfg\<close> \<open>wf_cfg cfg\<close> have "\<forall>k<K. s\<^sub>1 CHS ! k < G" by simp
    then have "\<forall>k<K. s\<^sub>1 CHS ! k \<in> set [0..<G]" by simp
    moreover
    from s\<^sub>1 have "length (s\<^sub>1 CHS) = K" by blast
    ultimately
    have "s\<^sub>1 CHS \<in> set (product_lists (replicate K [0..<G]))" by blast
    with \<open>hd (s\<^sub>1 ST) < Q\<close> show ?thesis by auto
  qed
  then have "index q_chs_enum_list (hd (s\<^sub>1 ST), s\<^sub>1 CHS) < q_chs_num"
    using q_chs_enum_list_length by fastforce
  ultimately
  obtain t_entrance where "t_entrance \<le> entrance_block_len" and
    "GOTO_on_List_Prog \<turnstile>\<^sub>l (pc_start, config_to_state cfg) \<rightarrow>\<^bsub>t_entrance\<^esub>
     (pc_start + 2 + index q_chs_enum_list (hd (s\<^sub>1 ST), s\<^sub>1 CHS), s\<^sub>1)"
    using entrance_block_length
    by (metis (no_types, lifting) add_2_eq_Suc less_imp_le_nat nat_add_left_cancel_le)
  with jump_to_correct_label
  have "GOTO_on_List_Prog \<turnstile>\<^sub>l (pc_start, config_to_state cfg) \<rightarrow>\<^bsub>t_entrance + 1\<^esub>
        (label_of_block_for_q_chs (hd (s\<^sub>1 ST), s\<^sub>1 CHS), s\<^sub>1)"
    by auto        
  with block_for_q_chs_correct
  have "GOTO_on_List_Prog \<turnstile>\<^sub>l (pc_start, config_to_state cfg)
        \<rightarrow>\<^bsub>t_entrance + 1 + block_for_q_chs_len\<^esub>
        (label_of_block_for_q_chs (hd (s\<^sub>1 ST), s\<^sub>1 CHS) + block_for_q_chs_len, s\<^sub>2)"
    by blast
  with jump_back_to_begin
  have "GOTO_on_List_Prog \<turnstile>\<^sub>l (pc_start, config_to_state cfg)
        \<rightarrow>\<^bsub>t_entrance + 1 + block_for_q_chs_len + 1\<^esub>
        (pc_start, s\<^sub>2)"
    by auto

  with \<open>t_entrance \<le> entrance_block_len\<close>
  have "\<exists>t_entrance \<le> entrance_block_len.
         GOTO_on_List_Prog \<turnstile>\<^sub>l  (pc_start, config_to_state cfg)
         \<rightarrow>\<^bsub>t_entrance + block_for_q_chs_len + 2\<^esub>
         (pc_start, s\<^sub>2)" by auto
  with \<open>s\<^sub>2 \<sim> cfg'\<close> \<open>wf_cfg cfg'\<close>
  show thesis using that by presburger
qed
    
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

lemma TM_to_GOTO_on_List_correct_and_in_linear_time':
  assumes "s \<sim> cfg"
      and "execute M cfg t = cfg'"
    shows "\<exists>c. \<exists>t' \<le> c * t.
          (GOTO_on_List_Prog \<turnstile>\<^sub>l (pc_start, s) \<rightarrow>\<^bsub>t'\<^esub> (pc_halt, s'))"
      and "s' \<sim> cfg'"
  using assms
   apply (induction t)
  sorry

theorem TM_to_GOTO_on_List_correct_and_in_linear_time:
  assumes "s \<sim> (0, TPS)"
    shows "\<exists>t \<le> T. \<exists>c. \<exists>t' \<le> c * t.
          (GOTO_on_List_Prog \<turnstile>\<^sub>l (pc_start, s) \<rightarrow>\<^bsub>t'\<^esub> (pc_halt, s'))"
      and "s' \<sim> (Q, TPS')"
proof -
  from runtime_M have execute_M: "\<exists>t \<le> T. execute M (0, TPS) t = (Q, TPS')"
    using Q unfolding transforms_def transits_def
    by simp
  with assms show
    "\<exists>t \<le> T. \<exists>c. \<exists>t' \<le> c * t.
     (GOTO_on_List_Prog \<turnstile>\<^sub>l (pc_start, s) \<rightarrow>\<^bsub>t'\<^esub> (pc_halt, s'))"
    using TM_to_GOTO_on_List_correct_and_in_linear_time'
    by (smt (verit, del_insts)
        append1_eq_conv append_assoc concat_map_singleton config_to_state.simps(2) list.inject)
  
  from assms execute_M
  show "s' \<sim> (Q, TPS')"
    using TM_to_GOTO_on_List_correct_and_in_linear_time'(2) by blast
qed

end
end