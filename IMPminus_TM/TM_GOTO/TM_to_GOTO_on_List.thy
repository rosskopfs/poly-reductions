theory TM_to_GOTO_on_List
  imports GOTO_on_List Cook_Levin.Basics "List-Index.List_Index" List_Extra TM_Extra
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
  assumes wf_TPS: "length TPS = K \<and>
                   (\<forall>k < K. \<forall>p < MAX_LEN. (TPS ::: k) p < G) \<and>
                   (\<forall>k < K. (TPS :#: k) < MAX_LEN)"
      and head_position_no_exceed_MAX_LEN:
          "\<forall>t \<le> T. \<forall>k < K. execute M (0, TPS) t <#> k < MAX_LEN"
begin

lemma head_position_no_exceed_MAX_LEN':
  "\<forall>k < K. execute M (0, TPS) t <#> k < MAX_LEN"
proof (cases "t \<le> T")
  case True
  then show ?thesis
    using head_position_no_exceed_MAX_LEN by blast
next
  case False
  from runtime_M obtain T\<^sub>0 where T\<^sub>0: "T\<^sub>0 \<le> T" "execute M (0, TPS) T\<^sub>0 = (Q, TPS')"
    by (metis Q halting_config_def transforms_halting_config transforms_running_time)
  then have "\<forall>k < K. (Q, TPS') <#> k < MAX_LEN"
    using head_position_no_exceed_MAX_LEN by fastforce
  moreover
  from T\<^sub>0 have "execute M (Q, TPS') (t - T\<^sub>0) = execute M (0, TPS) t"
    by (metis False dual_order.trans execute_additive le_add_diff_inverse nle_le)
  with T\<^sub>0 have "execute M (0, TPS) t = (Q, TPS')"
    by (metis Q diff_is_0_eq' execute.simps(1) execute_after_halting_ge fst_conv nless_le not_le_imp_less)
  ultimately
  show ?thesis by simp
qed

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
  "entrance_block_len \<equiv> q_chs_num + 2"
abbreviation block_for_q_chs_len :: nat where
  "block_for_q_chs_len \<equiv> 2 * K + 2"

fun label_of_block_for_q_chs :: "state \<times> symbol list \<Rightarrow> label" where
  "label_of_block_for_q_chs q_chs =
   entrance_block_len + block_for_q_chs_len * (index q_chs_enum_list q_chs) + 1"

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
          Left \<Rightarrow> MoveLeft n | Right \<Rightarrow> MoveRight n | Stay \<Rightarrow> NOP\<^sub>l]) \<comment> \<open>head movement\<close>
      [0..<K])) \<comment> \<open>for each tape\<close>
   @ [GOTO\<^sub>l pc_start]"

lemma block_for_q_chs_length: "length (block_for_q_chs q_act_s) = block_for_q_chs_len"
proof -
  let ?f = "(\<lambda>n. [
    TapeModify n (q_act_s [.] n),
    case q_act_s [~] n of
      Left \<Rightarrow> MoveLeft n | Right \<Rightarrow> MoveRight n | Stay \<Rightarrow> NOP\<^sub>l])"
  have "length (?f n) = 2" for n by auto
  then have "\<forall>xs \<in> set (map ?f [0..<K]). length xs = 2"
    by simp
  then have "length (concat (map ?f [0..<K])) = 2 * K"
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
  from block_for_q_chs_length
  have "\<forall>q_chs \<in> set q_chs_enum_list. length (?f q_chs) = block_for_q_chs_len" by fast
  then have "\<forall>blk \<in> set (map ?f q_chs_enum_list). length blk = block_for_q_chs_len" by simp
  then have "length blocks_for_actions = block_for_q_chs_len * (length q_chs_enum_list)"
    using length_concat_same_length [where ?xss = "map ?f q_chs_enum_list"]
    by fastforce
  then show ?thesis
    using q_chs_enum_list_length by presburger
qed

abbreviation GOTO_on_List_Prog :: "GOTO\<^sub>l_prog" where
  "GOTO_on_List_Prog \<equiv> entrance_block @ blocks_for_actions"

lemma label_of_block_for_q_chs_range:
  assumes "q_chs \<in> set q_chs_enum_list"
    shows "label_of_block_for_q_chs q_chs + block_for_q_chs_len - 1 \<le> length GOTO_on_List_Prog"
proof -
  from assms have "index q_chs_enum_list q_chs < q_chs_num"
    using q_chs_enum_list_length by auto
  then have "index q_chs_enum_list q_chs \<le> q_chs_num - 1"
    by linarith
  then have "block_for_q_chs_len * (index q_chs_enum_list q_chs) \<le>
             block_for_q_chs_len * q_chs_num - block_for_q_chs_len"
    by (metis mult.comm_neutral mult_le_mono2 right_diff_distrib')
  then have "block_for_q_chs_len * (index q_chs_enum_list q_chs) + block_for_q_chs_len \<le>
             block_for_q_chs_len * q_chs_num - block_for_q_chs_len + block_for_q_chs_len"
    by linarith
  moreover
  from assms have "0 < q_chs_num"
    using q_chs_enum_list_length
    by (metis length_pos_if_in_set)
  then have "block_for_q_chs_len * q_chs_num - block_for_q_chs_len + block_for_q_chs_len =
             block_for_q_chs_len * q_chs_num"
    by (metis add.commute add_diff_inverse_nat mult_numeral_1_right nat_mult_less_cancel_disj not_less_eq numeral_1_eq_Suc_0)
  ultimately
  have "block_for_q_chs_len * (index q_chs_enum_list q_chs) + block_for_q_chs_len \<le>
        length blocks_for_actions"
    using blocks_for_actions_length by argo
  then have "entrance_block_len + block_for_q_chs_len * (index q_chs_enum_list q_chs) + block_for_q_chs_len
             \<le> length GOTO_on_List_Prog"
    using entrance_block_length by force
  then show ?thesis by simp
qed

lemma search_table_content_by_index [simp]:
  assumes "i < q_chs_num"
    shows "GOTO_on_List_Prog !! (pc_start + 2 + i) =
           (\<lambda>(q, chs). IF ST = L [q] AND CHS = L chs THEN GOTO\<^sub>l label_of_block_for_q_chs (q, chs))
                      (q_chs_enum_list ! i)"
proof -
  let ?f = "\<lambda>(q, chs). IF ST = L [q] AND CHS = L chs THEN GOTO\<^sub>l label_of_block_for_q_chs (q, chs)"
  from assms have "pc_start + 2 + i \<le> entrance_block_len" by simp
  moreover
  have "entrance_block !! (pc_start + 2 + i) = map ?f q_chs_enum_list !! Suc i"
    by force
  with \<open>i < q_chs_num\<close> have "entrance_block !! (pc_start + 2 + i) = map ?f q_chs_enum_list ! i"
    using inth_nth [where ?i = "Suc i"] q_chs_enum_list_length
    by (smt (verit) Suc_leI diff_Suc_1 length_map zero_less_Suc)
  ultimately
  have "GOTO_on_List_Prog !! (pc_start + 2 + i) = map ?f q_chs_enum_list ! i"
    using q_chs_enum_list_length entrance_block_length
    using inth_append_in_fst_list [where ?i = "pc_start + 2 + i" and ?xs = entrance_block and ?ys = blocks_for_actions]
    by (metis (no_types, lifting) add_is_0 less_2_cases_iff list.size(3) not_gr0)
  with \<open>i < q_chs_num\<close> q_chs_enum_list_length
  show "GOTO_on_List_Prog !! (pc_start + 2 + i) = ?f (q_chs_enum_list ! i)"
    by auto
qed

lemma search_table_content_by_q_chs [simp]:
  assumes "(q, chs) \<in> set q_chs_enum_list"
    shows "GOTO_on_List_Prog !! (pc_start + 2 + index q_chs_enum_list (q, chs)) =
           IF ST = L [q] AND CHS = L chs THEN GOTO\<^sub>l label_of_block_for_q_chs (q, chs)"
proof -
  let ?f = "\<lambda>(q, chs). IF ST = L [q] AND CHS = L chs THEN GOTO\<^sub>l label_of_block_for_q_chs (q, chs)"
  have "\<forall>i < q_chs_num. GOTO_on_List_Prog !! (pc_start + 2 + i) = ?f (q_chs_enum_list ! i)"
    using search_table_content_by_index by blast
  moreover
  from \<open>(q, chs) \<in> set q_chs_enum_list\<close> have "q_chs_enum_list ! index q_chs_enum_list (q, chs) = (q, chs)"
    by fastforce
  moreover
  from \<open>(q, chs) \<in> set q_chs_enum_list\<close> have "index q_chs_enum_list (q, chs) < q_chs_num"
    by (metis index_less_size_conv q_chs_enum_list_length)
  ultimately
  show ?thesis
    by (metis (no_types, lifting) case_prod_conv)
qed

lemma inth_GOTO_on_List_Prog_label_of_block_for_q_chs:
  assumes "(q, chs) \<in> set q_chs_enum_list"
      and "0 \<le> i \<and> i < block_for_q_chs_len"
    shows "GOTO_on_List_Prog !! (label_of_block_for_q_chs (q, chs) + i) =
           block_for_q_chs ((M!q) chs) ! i"
proof -
  let ?blks = "map (\<lambda>(q, chs). block_for_q_chs ((M!q) chs)) q_chs_enum_list"
  have "\<forall>(q, chs) \<in> set q_chs_enum_list. length (block_for_q_chs ((M!q) chs)) = block_for_q_chs_len"
    using block_for_q_chs_length by blast
  then have same_length: "\<forall>blk \<in> set (map (\<lambda>(q, chs). block_for_q_chs ((M!q) chs)) q_chs_enum_list).
                          length blk = block_for_q_chs_len"
    by simp
  moreover
  from \<open>(q, chs) \<in> set q_chs_enum_list\<close> have idx_lt_length: "index q_chs_enum_list (q, chs) < length ?blks"
    by simp
  moreover
  from assms(2) have Suc_i_range: "0 < 1 + i \<and> 1 + i \<le> block_for_q_chs_len" by auto
  ultimately
  have "blocks_for_actions !! (block_for_q_chs_len * (index q_chs_enum_list (q, chs)) + 1 + i) =
        ?blks ! (index q_chs_enum_list (q, chs)) !! (1 + i)"
    using inth_concat_same_length [where ?xss = ?blks and ?i = "1 + i" and ?n = "index q_chs_enum_list (q, chs)"
                                    and ?len = block_for_q_chs_len]
    by (metis (no_types, lifting) ab_semigroup_add_class.add_ac(1) mult.commute)
  then have "blocks_for_actions !! (block_for_q_chs_len * (index q_chs_enum_list (q, chs)) + 1 + i) =
             ?blks ! (index q_chs_enum_list (q, chs)) ! i"
    using inth_nth [where ?i = "1 + i" and ?xs = "?blks ! (index q_chs_enum_list (q, chs))"]
    using Suc_i_range same_length idx_lt_length
    by (metis diff_add_inverse nth_mem)
  moreover
  from \<open>(q, chs) \<in> set q_chs_enum_list\<close>
  have "?blks ! (index q_chs_enum_list (q, chs)) = block_for_q_chs ((M!q) chs)"
    by auto
  ultimately
  have "blocks_for_actions !! (block_for_q_chs_len * (index q_chs_enum_list (q, chs)) + 1 + i) =
        block_for_q_chs ((M!q) chs) ! i"
    by argo
  moreover
  from assms(2) have "0 < block_for_q_chs_len * index q_chs_enum_list (q, chs) + 1 + i" by linarith
  ultimately
  have "GOTO_on_List_Prog !! (length entrance_block + (block_for_q_chs_len * index q_chs_enum_list (q, chs) + 1 + i)) =
        block_for_q_chs ((M ! q) chs) ! i"
    using inth_append_in_snd_list [where ?i = "block_for_q_chs_len * index q_chs_enum_list (q, chs) + 1 + i"
                                     and ?xs = entrance_block and ?ys = blocks_for_actions]
    by presburger
  moreover
  have "length entrance_block + (block_for_q_chs_len * index q_chs_enum_list (q, chs) + 1 + i) =
        label_of_block_for_q_chs (q, chs) + i"
    using entrance_block_length
    using label_of_block_for_q_chs.simps [where ?q_chs = "(q, chs)"]
    by presburger
  ultimately
  show ?thesis by argo
qed

lemma state_update_by_index:
  assumes "(q, chs) \<in> set q_chs_enum_list"
    shows "GOTO_on_List_Prog !! (label_of_block_for_q_chs (q, chs)) =
           ST ::=\<^sub>l L [[*] ((M!q) chs)]"
proof -
  from assms
  have "GOTO_on_List_Prog !! (label_of_block_for_q_chs (q, chs)) = block_for_q_chs ((M!q) chs) ! 0"
    using inth_GOTO_on_List_Prog_label_of_block_for_q_chs [where ?i = 0 and ?q = q and ?chs = chs]
    by (metis (no_types, lifting) Nat.add_0_right add_is_0 le_numeral_extra(3) neq0_conv zero_neq_numeral)
  also have "... = ST ::=\<^sub>l L [[*] ((M!q) chs)]"
    unfolding block_for_q_chs.simps by auto
  finally show ?thesis by blast
qed

lemma tape_modify_by_index:
  assumes "(q, chs) \<in> set q_chs_enum_list"
      and "n < K"
    shows "GOTO_on_List_Prog !! (label_of_block_for_q_chs (q, chs) + 1 + 2 * n) =
           TapeModify n (((M!q) chs) [.] n)"
proof -
  let ?f = "(\<lambda>n. [TapeModify n ((M!q) chs [.] n),
                  case (M!q) chs [~] n of Left \<Rightarrow> MoveLeft n | Right \<Rightarrow> MoveRight n | Stay \<Rightarrow> NOP\<^sub>l])"
  have same_length: "\<forall>xs \<in> set (map ?f [0..<K]). length xs = 2" by force
  then have "length (concat (map ?f [0..<K])) = 2 * K"
    using length_concat_same_length [where ?xss = "map ?f [0..<K]" and ?len = 2] by auto
  with \<open>n < K\<close> have "2 * n < length (concat (map ?f [0..<K]))" by simp

  from \<open>n < K\<close> have "1 + 2 * n < block_for_q_chs_len"
    using add.assoc by force
  with assms(1)
  have "GOTO_on_List_Prog !! (label_of_block_for_q_chs (q, chs) + 1 + 2 * n) =
        block_for_q_chs ((M!q) chs) ! (1 + 2 * n)"
    using inth_GOTO_on_List_Prog_label_of_block_for_q_chs [where ?i = "1 + 2 * n" and ?q = q and ?chs = chs]
    by (smt (verit) ab_semigroup_add_class.add_ac(1) le0)
  also have "... = (concat (map ?f [0..<K]) @ [GOTO\<^sub>l pc_start]) ! (2 * n)"
    unfolding block_for_q_chs.simps
    using nth_Cons_pos [where ?n = "1 + 2 * n" and ?x = "ST ::=\<^sub>l L [[*] ((M!q) chs)]"
                          and ?xs = "(concat (map ?f [0..<K]) @ [GOTO\<^sub>l pc_start])"]
    by auto
  also have "... = concat (map ?f [0..<K]) ! (2 * n)"
    using nth_append [where ?xs = "concat (map ?f [0..<K])" and ?ys = "[GOTO\<^sub>l pc_start]"
                        and ?n = "2 * n"]
    using \<open>2 * n < length (concat (map ?f [0..<K]))\<close>
    by presburger
  also have "... = map ?f [0..<K] ! n ! 0"
    using nth_concat_same_length [where ?xss = "map ?f [0..<K]" and ?i = 0 and ?len = 2 and ?n = n]
    using same_length \<open>n < K\<close>
    by (simp add: mult.commute)
  also have "... = ?f n ! 0"
    using \<open>n < K\<close> by simp
  also have "... = TapeModify n (((M!q) chs) [.] n)" by simp
  finally show ?thesis by fast
qed

lemma head_move_by_index:
  assumes "(q, chs) \<in> set q_chs_enum_list"
      and "n < K"
    shows "GOTO_on_List_Prog !! (label_of_block_for_q_chs (q, chs) + 2 + 2 * n) =
           (case ((M!q) chs) [~] n of Left \<Rightarrow> MoveLeft n | Right \<Rightarrow> MoveRight n | Stay \<Rightarrow> NOP\<^sub>l)"
proof -
  let ?f = "(\<lambda>n. [TapeModify n ((M!q) chs [.] n),
                  case (M!q) chs [~] n of Left \<Rightarrow> MoveLeft n | Right \<Rightarrow> MoveRight n | Stay \<Rightarrow> NOP\<^sub>l])"
  have same_length: "\<forall>xs \<in> set (map ?f [0..<K]). length xs = 2" by force
  then have "length (concat (map ?f [0..<K])) = 2 * K"
    using length_concat_same_length [where ?xss = "map ?f [0..<K]" and ?len = 2] by auto
  with \<open>n < K\<close> have "1 + 2 * n < length (concat (map ?f [0..<K]))" by simp

  from \<open>n < K\<close> have "2 + 2 * n < block_for_q_chs_len"
    using add.assoc by force
  with assms(1)
  have "GOTO_on_List_Prog !! (label_of_block_for_q_chs (q, chs) + 2 + 2 * n) =
        block_for_q_chs ((M!q) chs) ! (2 + 2 * n)"
    using inth_GOTO_on_List_Prog_label_of_block_for_q_chs [where ?i = "2 + 2 * n" and ?q = q and ?chs = chs]
    by (smt (verit) ab_semigroup_add_class.add_ac(1) le0)
  also have "... = (concat (map ?f [0..<K]) @ [GOTO\<^sub>l pc_start]) ! (1 + 2 * n)"
    unfolding block_for_q_chs.simps
    using nth_Cons_pos by auto
  also have "... = concat (map ?f [0..<K]) ! (1 + 2 * n)"
    using nth_append [where ?xs = "concat (map ?f [0..<K])" and ?ys = "[GOTO\<^sub>l pc_start]"
                        and ?n = "1 + 2 * n"]
    using \<open>1 + 2 * n < length (concat (map ?f [0..<K]))\<close> try0
    by presburger
  also have "... = map ?f [0..<K] ! n ! 1"
    using nth_concat_same_length [where ?xss = "map ?f [0..<K]" and ?i = 1 and ?len = 2 and ?n = n]
    using same_length \<open>n < K\<close>
    by (simp add: mult.commute)
  also have "... = ?f n ! 1"
    using \<open>n < K\<close>
    by (smt (verit) minus_nat.diff_0 nth_map_upt plus_nat.add_0)
  also have "... = (case ((M!q) chs) [~] n of Left \<Rightarrow> MoveLeft n | Right \<Rightarrow> MoveRight n | Stay \<Rightarrow> NOP\<^sub>l)"
    by simp
  finally show ?thesis by fast
qed

lemma goto_start_by_index:
  assumes "(q, chs) \<in> set q_chs_enum_list"
    shows "GOTO_on_List_Prog !! (label_of_block_for_q_chs (q, chs) + (block_for_q_chs_len - 1)) =
           GOTO\<^sub>l pc_start"
proof -
  from assms
  have "GOTO_on_List_Prog !! (label_of_block_for_q_chs (q, chs) + (block_for_q_chs_len - 1)) =
        block_for_q_chs ((M!q) chs) ! (block_for_q_chs_len - 1)"
    using inth_GOTO_on_List_Prog_label_of_block_for_q_chs
          [where ?i = "block_for_q_chs_len - 1" and ?q = q and ?chs = chs]
    by linarith
  also have "... = block_for_q_chs ((M!q) chs) ! (length (block_for_q_chs ((M!q) chs)) - 1)"
    using block_for_q_chs_length [of "(M!q) chs"] by argo
  also have "... = GOTO\<^sub>l pc_start" by simp
  finally show ?thesis by blast
qed


subsection \<open>Properties about state and configuration and their preservation\<close>
text \<open>The verification requires some properties about the state of the GOTO_on_List program,
as well as the corresponding TM configuration. Below are some definitions and lemma about them
and their preservation through execution.\<close>

definition configuration_of_prog_same_to_TM :: "state\<^sub>l \<Rightarrow> config \<Rightarrow> bool" (\<open>_ \<sim> _\<close> 50) where
  "s \<sim> cfg \<equiv>
    s ST = [fst cfg] \<and> \<comment>\<open>state\<close>
    (\<forall>k < K. s (HP k) = [cfg <#> k]) \<and> \<comment>\<open>head positions of each tape\<close>
    (\<forall>k < K. \<forall>p < MAX_LEN. (s (TP k)) ! p = (cfg <:> k) p)" \<comment>\<open>tape content\<close>

lemma configuration_of_prog_same_to_TM_D [intro]:
  assumes "s \<sim> cfg"
    shows "s ST = [fst cfg]"
      and "\<forall>k < K. s (HP k) = [cfg <#> k]"
      and "\<forall>k < K. \<forall>p < MAX_LEN. (s (TP k)) ! p = (cfg <:> k) p"
  using assms configuration_of_prog_same_to_TM_def by simp_all

lemma configuration_of_prog_same_to_TM_I:
  assumes "s ST = [fst cfg]"
      and "\<forall>k < K. s (HP k) = [cfg <#> k]"
      and "\<forall>k < K. \<forall>p < MAX_LEN. (s (TP k)) ! p = (cfg <:> k) p"
    shows "s \<sim> cfg"
  unfolding configuration_of_prog_same_to_TM_def
  using assms by blast

definition wf_cfg :: "config \<Rightarrow> bool" where
  "wf_cfg cfg \<equiv>
    fst cfg \<le> Q \<and> \<comment>\<open>state, = Q means halting state\<close>
    ||cfg|| = K \<and> \<comment>\<open>number of tapes\<close>
    (\<forall>k < K. \<forall>p < MAX_LEN. (cfg <:> k) p < G) \<and> \<comment>\<open>tape content consists of characters < G only\<close>
    (\<forall>k < K. cfg <#> k < MAX_LEN)" \<comment>\<open>tape head position not exceeding max used length of tape\<close>

lemma wf_cfg_D [intro]:
  assumes "wf_cfg cfg"
    shows "fst cfg \<le> Q"
      and "||cfg|| = K"
      and "\<forall>k < K. \<forall>p < MAX_LEN. (cfg <:> k) p < G"
      and "\<forall>k < K. cfg <#> k < MAX_LEN"
  using assms wf_cfg_def by simp_all

lemma wf_cfg_I:
  assumes "fst cfg \<le> Q"
      and "||cfg|| = K"
      and "\<forall>k < K. \<forall>p < MAX_LEN. (cfg <:> k) p < G"
      and "\<forall>k < K. cfg <#> k < MAX_LEN"
    shows "wf_cfg cfg"
  unfolding wf_cfg_def
  using assms by blast

lemma wf_cfg_start_cfg: "wf_cfg (0, TPS)"
  using wf_TPS
  by (simp add: wf_cfg_def)

lemma wf_cfg_preserved_by_execute [intro]:
  assumes "execute M (0, TPS) t = cfg'"
    shows "wf_cfg cfg'"
  using assms
proof (induction t arbitrary: cfg')
  case 0
  then show ?case
    using wf_cfg_start_cfg by auto
next
  case (Suc t)
  then obtain cfg where cfg: "execute M (0, TPS) t = cfg" and exe: "exe M cfg = cfg'"
    by auto
  with Suc.IH exe have "wf_cfg cfg" by blast
  then show ?case
  proof (cases "fst cfg < Q")
    case True
    from TM exe \<open>wf_cfg cfg\<close> have "fst cfg' \<le> Q"
      using Q exe_state_valid wf_cfg_D(1-2) by auto
    moreover
    from \<open>wf_cfg cfg\<close> have "||cfg|| = K" by blast
    with exe TM have "||cfg'|| = K"
      using exe_num_tapes by metis
    moreover
    from Suc.prems have "\<forall>k < K. cfg' <#> k < MAX_LEN"
      using head_position_no_exceed_MAX_LEN' by blast
    moreover
    from cfg have "\<forall>k < K. cfg <#> k < MAX_LEN"
      using head_position_no_exceed_MAX_LEN' by blast
    then have "\<forall>k < K. \<forall>p < MAX_LEN. (cfg' <:> k) p < G"
      using tape_content_valid
      using TM \<open>wf_cfg cfg\<close> \<open>||cfg|| = K\<close> exe wf_cfg_D(3) by blast
    ultimately
    show ?thesis by (simp add: wf_cfg_I)
  next
    case False
    with \<open>wf_cfg cfg\<close> have "fst cfg = Q"
      using le_neq_implies_less by blast
    with \<open>exe M cfg = cfg'\<close> have "cfg' = cfg"
      using exe_ge_length Q by simp
    with \<open>wf_cfg cfg\<close> show ?thesis by blast
  qed
qed


abbreviation read_chars_correspond_to_cfg :: "state\<^sub>l \<Rightarrow> config \<Rightarrow> bool" where
  "read_chars_correspond_to_cfg s cfg \<equiv> (\<forall>k < K. s CHS ! k = cfg <.> k) \<and> length (s CHS) = K"

lemma tape_content_to_list_length [simp]:
  "length (tape_content_to_list tp len) = len"
  by (induction len) auto

lemma tape_content_to_list_correct [intro]:
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
  using tape_content_to_list_correct configuration_of_prog_same_to_TM_I
  by (metis config_to_state.simps(1-3) surjective_pairing)

lemma proper_state_q_chs_in_enum_list [intro]:
  assumes "\<exists>t. execute M (0, TPS) t = cfg"
      and "s \<sim> cfg"
      and "fst cfg < Q"
      and "read_chars_correspond_to_cfg s cfg"
    shows "(hd (s ST), s CHS) \<in> set q_chs_enum_list"
proof -
  from wf_cfg_preserved_by_execute assms(1) have "wf_cfg cfg" by blast
  from \<open>fst cfg < Q\<close> \<open>s \<sim> cfg\<close> have "hd (s ST) < Q"
    by (simp add: configuration_of_prog_same_to_TM_D(1))
  moreover
  from \<open>read_chars_correspond_to_cfg s cfg\<close> have "length (s CHS) = K" by blast
  from \<open>wf_cfg cfg\<close> \<open>read_chars_correspond_to_cfg s cfg\<close> have "\<forall>k < K. s CHS ! k < G"
    by (simp add: wf_cfg_D(3) wf_cfg_D(4))
  with \<open>length (s CHS) = K\<close> have "s CHS \<in> set (product_lists (replicate K [0..<G]))"
    by auto
  ultimately
  show ?thesis by force
qed

subsection \<open>Correctness of the transform function\<close>
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
   ("block_for_q_chs_len - 1" steps; pc "label_of_block_for_q_chs (q, chs)" -> "label_of_block_for_q_chs (q, chs) + block_for_q_chs_len - 1")
5. jump to the beginning of the program
   (1 step; pc "label_of_block_for_q_chs (q, chs) + block_for_q_chs_len - 1" -> 1)
Each of these 5 parts are either sequentially executed with no jump, or a single jump.
Below first shows that each of them are correct, then the correctness of the program for each single TM step.\<close>

lemma read_state_and_chars_correct:
  assumes "\<exists>t. execute M (0, TPS) t = cfg"
      and "s \<sim> cfg"
      and "fst cfg < Q" \<comment>\<open>not in halting state\<close>
  obtains s'
    where "GOTO_on_List_Prog \<turnstile>\<^sub>l (pc_start, s) \<rightarrow>\<^bsub>2\<^esub> (pc_start + 2, s')"
      and "s' \<sim> cfg"
      and "read_chars_correspond_to_cfg s' cfg"
proof -
  from wf_cfg_preserved_by_execute assms(1) have "wf_cfg cfg" by blast
  from \<open>fst cfg < Q\<close> \<open>s \<sim> cfg\<close>
  have "s ST \<noteq> [Q]"
    by (simp add: configuration_of_prog_same_to_TM_D(1)) 
  then have "GOTO_on_List_Prog \<turnstile>\<^sub>l (pc_start, s) \<rightarrow> (pc_start + 1, s)"
    by auto
  then have first_step: "GOTO_on_List_Prog \<turnstile>\<^sub>l (pc_start, s) \<rightarrow>\<^bsub>1\<^esub> (pc_start + 1, s)"
    by blast
  let ?s' = "snd (iexec\<^sub>l (CHS ::=\<^sub>l ReadChs [0..<K]) (pc_start + 1, s))"
  let ?chs = "map (\<lambda>n. (s (TP n)) ! (hd (s (HP n)))) [0..<K]"
  have "?s' CHS = ?chs" by auto
  from \<open>s \<sim> cfg\<close> have "\<forall>k < K. (s (TP k)) ! (hd (s (HP k))) = cfg <.> k"
    using TM_to_GOTO_on_List.wf_cfg_D(4) TM_to_GOTO_on_List_axioms \<open>wf_cfg cfg\<close>
          configuration_of_prog_same_to_TM_def
    by auto
  with \<open>s \<sim> cfg\<close> \<open>?s' CHS = ?chs\<close> have "read_chars_correspond_to_cfg ?s' cfg"
    using length_upt by force
  moreover
  have "GOTO_on_List_Prog \<turnstile>\<^sub>l (pc_start + 1, s) \<rightarrow> (pc_start + 2, ?s')" by auto
  then have "GOTO_on_List_Prog \<turnstile>\<^sub>l (pc_start + 1, s) \<rightarrow>\<^bsub>1\<^esub> (pc_start + 2, ?s')" by blast
  with first_step have "GOTO_on_List_Prog \<turnstile>\<^sub>l (pc_start, s) \<rightarrow>\<^bsub>2\<^esub> (pc_start + 2, ?s')"
    using exec\<^sub>l_t_add [where ?P = GOTO_on_List_Prog and ?s = s and ?s' = s and ?s'' = ?s'
        and ?pc = pc_start and ?pc' = "pc_start + 1" and ?pc'' = "pc_start + 2" and ?t\<^sub>1 = 1 and ?t\<^sub>2 = 1]
    by (metis nat_1_add_1)
  moreover
  have "?s' = s(CHS := ?chs)" by simp
  then have "?s' ST = s ST" "\<forall>n. ?s' (TP n) = s (TP n)" "\<forall>n. ?s' (HP n) = s (HP n)" by simp+
  with \<open>s \<sim> cfg\<close> have "?s' \<sim> cfg"
    by (simp add: configuration_of_prog_same_to_TM_def)
  ultimately
  show thesis using that by blast
qed

lemma search_for_correct_label_for_q_and_chs:
  assumes "\<exists>t. execute M (0, TPS) t = cfg"
      and "s \<sim> cfg"
      and "fst cfg < Q"
      and "read_chars_correspond_to_cfg s cfg"
    shows "GOTO_on_List_Prog \<turnstile>\<^sub>l
           (pc_start + 2, s) \<rightarrow>\<^bsub>index q_chs_enum_list (hd (s ST), s CHS)\<^esub>
           (pc_start + 2 + index q_chs_enum_list (hd (s ST), s CHS), s)"
proof -
  let ?a = "pc_start + 2"
  let ?q_chs = "(hd (s ST), s CHS)"
  let ?len = "index q_chs_enum_list ?q_chs"
  let ?f = "\<lambda>(q, chs). IF ST = L [q] AND CHS = L chs THEN GOTO\<^sub>l label_of_block_for_q_chs (q, chs)"
  from assms have "?q_chs \<in> set q_chs_enum_list"
    using proper_state_q_chs_in_enum_list by blast
  then have "?len < q_chs_num"
    by (metis index_less_size_conv q_chs_enum_list_length)
  then have "?a + ?len \<le> length GOTO_on_List_Prog"
    using q_chs_enum_list_length entrance_block_length by force
  moreover
  have "\<forall>i. ?a \<le> i \<and> i < ?a + ?len \<longrightarrow>
    no_jump s (GOTO_on_List_Prog !! i) \<and> no_modification (GOTO_on_List_Prog !! i)"
  proof (standard; standard)
    fix i assume "?a \<le> i \<and> i < ?a + ?len"
    with \<open>?len < q_chs_num\<close> have "GOTO_on_List_Prog !! i = ?f (q_chs_enum_list ! (i - ?a))"
      using search_table_content_by_index [where ?i = "i - ?a"]
      by (smt (verit, ccfv_SIG) add_diff_inverse_nat add_lessD1 diff_is_0_eq' length_greater_0_conv
          less_imp_add_positive list.size(3) nat_add_left_cancel_less zero_less_diff) 
    moreover
    have "no_modification (?f (q_chs_enum_list ! (i - ?a)))"
      by (smt (verit) no_modification.simps(9) old.prod.case surj_pair)
    moreover
    have "no_jump s (?f (q_chs_enum_list ! (i - ?a)))"
    proof -
      from \<open>?a \<le> i \<and> i < ?a + ?len\<close> \<open>?q_chs \<in> set q_chs_enum_list\<close>
      have "q_chs_enum_list ! (i - ?a) \<noteq> q_chs_enum_list ! ?len"
        using q_chs_enum_list_distinct
        by (metis diff_add_inverse diff_less_mono index_first nth_index)
      moreover
      from \<open>read_chars_correspond_to_cfg s cfg\<close> \<open>?q_chs \<in> set q_chs_enum_list\<close>
      have "?q_chs = q_chs_enum_list ! ?len" by simp
      ultimately
      have "?q_chs \<noteq> q_chs_enum_list ! (i - ?a)" by argo
      then have "s ST \<noteq> [fst (q_chs_enum_list ! (i - ?a))] \<or> s CHS \<noteq> snd (q_chs_enum_list ! (i - ?a))"
        by auto
      then have "s ST \<noteq> eval_GOTO\<^sub>l_operi s (L [fst (q_chs_enum_list ! (i - ?a))]) \<or>
                 s CHS \<noteq> eval_GOTO\<^sub>l_operi s (L (snd (q_chs_enum_list ! (i - ?a))))"
        by simp
      then show ?thesis
        by (simp add: case_prod_beta)
    qed
    ultimately
    show "no_jump s (GOTO_on_List_Prog !! i) \<and> no_modification (GOTO_on_List_Prog !! i)"
      by presburger
  qed
  then show ?thesis
    using execute_prog_no_jump_and_no_modification
    using calculation plus_1_eq_Suc by auto
qed

lemma jump_to_correct_label:
  assumes "\<exists>t. execute M (0, TPS) t = cfg"
      and "s \<sim> cfg"
      and "fst cfg < Q"
      and "read_chars_correspond_to_cfg s cfg"
    shows "GOTO_on_List_Prog \<turnstile>\<^sub>l
           (pc_start + 2 + index q_chs_enum_list (hd (s ST), s CHS), s) \<rightarrow>
           (label_of_block_for_q_chs (hd (s ST), s CHS), s)"
proof -
  let ?f = "\<lambda>(q, chs). IF ST = L [q] AND CHS = L chs THEN GOTO\<^sub>l label_of_block_for_q_chs (q, chs)"
  let ?q_chs = "(hd (s ST), s CHS)"
  let ?pc = "pc_start + 2 + index q_chs_enum_list ?q_chs"

  from assms have "?q_chs \<in> set q_chs_enum_list"
    using proper_state_q_chs_in_enum_list by blast
  then have "GOTO_on_List_Prog !! ?pc = ?f ?q_chs"
    using search_table_content_by_q_chs by fast
  moreover
  have "0 < ?pc" by linarith
  moreover
  from \<open>?q_chs \<in> set q_chs_enum_list\<close> have "index q_chs_enum_list ?q_chs < q_chs_num"
    by (metis index_less_size_conv q_chs_enum_list_length)
  then have "?pc \<le> pc_start + 2 + q_chs_num - 1" by simp
  then have "?pc \<le> entrance_block_len" by auto
  then have "?pc \<le> length GOTO_on_List_Prog"
    using entrance_block_length by fastforce
  moreover
  have "s ST = eval_GOTO\<^sub>l_operi s (L [fst ?q_chs]) \<and> s CHS = eval_GOTO\<^sub>l_operi s (L (snd ?q_chs))"
    using configuration_of_prog_same_to_TM_def TM_to_GOTO_on_List_axioms assms(2) by auto
  then have "iexec\<^sub>l (?f ?q_chs) (?pc, s) = (label_of_block_for_q_chs ?q_chs, s)"
    by force
  ultimately
  show ?thesis
    by (metis (no_types, lifting) bot_nat_0.extremum_uniqueI exec1\<^sub>l_I length_0_conv length_greater_0_conv)
qed

lemma block_for_q_chs_correct:
  assumes "\<exists>t. execute M (0, TPS) t = cfg"
      and "s \<sim> cfg"
      and "fst cfg < Q"
      and "read_chars_correspond_to_cfg s cfg"
      and "exe M cfg = cfg'"
  obtains s'
    where "GOTO_on_List_Prog \<turnstile>\<^sub>l
           (label_of_block_for_q_chs (hd (s ST), s CHS), s) \<rightarrow>\<^bsub>block_for_q_chs_len - 1\<^esub>
           (label_of_block_for_q_chs (hd (s ST), s CHS) + block_for_q_chs_len - 1, s')"
      and "s' \<sim> cfg'"
proof -
  let ?q = "hd (s ST)"
  let ?chs = "s CHS"
  let ?q_chs = "(hd (s ST), s CHS)"
  let ?label = "label_of_block_for_q_chs ?q_chs"
  let ?len = "block_for_q_chs_len - 1"

  from assms have "?q_chs \<in> set q_chs_enum_list"
    using proper_state_q_chs_in_enum_list by blast
  then have "?label \<le> length GOTO_on_List_Prog"
    using label_of_block_for_q_chs_range
    by (smt (verit) Nat.add_diff_assoc le_add1 le_add2 le_trans nat_1_add_1)
  moreover
  have "\<forall>cmd \<in> set (butlast (block_for_q_chs ((M!?q) ?chs))). strict_no_jump cmd"
    unfolding block_for_q_chs.simps sorry
  have block_strict_no_jump:
    "\<forall>i. ?label \<le> i \<and> i < ?label + ?len \<longrightarrow> strict_no_jump (GOTO_on_List_Prog !! i)"
    sorry
  show thesis sorry
qed

lemma jump_back_to_begin:
  assumes "\<exists>t. execute M (0, TPS) t = cfg"
      and "s \<sim> cfg"
      and "fst cfg < Q"
      and "read_chars_correspond_to_cfg s cfg"
    shows "GOTO_on_List_Prog \<turnstile>\<^sub>l
           (label_of_block_for_q_chs (hd (s ST), s CHS) + block_for_q_chs_len - 1, s') \<rightarrow>
           (pc_start, s')"
proof -
  let ?q_chs = "(hd (s ST), s CHS)"
  let ?pc = "label_of_block_for_q_chs (hd (s ST), s CHS) + block_for_q_chs_len - 1"
  from assms have "?q_chs \<in> set q_chs_enum_list"
    using proper_state_q_chs_in_enum_list by blast
  then have "GOTO_on_List_Prog !! ?pc = GOTO\<^sub>l pc_start"
    using goto_start_by_index [where ?q = "hd (s ST)" and ?chs = "s CHS"]
    by (metis (no_types, lifting) Nat.diff_add_assoc add_leE le_add2 nat_1_add_1)
  moreover
  have "iexec\<^sub>l (GOTO\<^sub>l pc_start) (?pc, s) = (pc_start, s)" by simp
  moreover
  have "0 < ?pc" by linarith
  moreover
  from \<open>?q_chs \<in> set q_chs_enum_list\<close> have "?pc \<le> length GOTO_on_List_Prog"
    using label_of_block_for_q_chs_range by blast 
  ultimately
  show ?thesis
    by (metis (no_types, lifting) Nil_is_append_conv exec1\<^sub>l_I iexec\<^sub>l.simps(7) list.distinct(1))
qed

corollary TM_to_GOTO_on_List_correct_for_single_step:
  assumes "\<exists>t. execute M (0, TPS) t = cfg"
      and "fst cfg < Q"
      and "exe M cfg = cfg'"
      and "s \<sim> cfg"
    obtains s'
    where "\<exists>t_entrance \<le> entrance_block_len.
           GOTO_on_List_Prog \<turnstile>\<^sub>l
           (pc_start, s)
           \<rightarrow>\<^bsub>t_entrance + block_for_q_chs_len + 1\<^esub>
           (pc_start, s')"
      and "s' \<sim> cfg'"
proof -
  from wf_cfg_preserved_by_execute assms(1) have "wf_cfg cfg" by blast

  from assms(1) \<open>fst cfg < Q\<close> \<open>s \<sim> cfg\<close> obtain s\<^sub>1 where read_state_and_chars_correct:
    "GOTO_on_List_Prog \<turnstile>\<^sub>l (pc_start, s) \<rightarrow>\<^bsub>2\<^esub> (pc_start + 2, s\<^sub>1)"
    and s\<^sub>1: "s\<^sub>1 \<sim> cfg" "read_chars_correspond_to_cfg s\<^sub>1 cfg"
    using read_state_and_chars_correct by blast
  with assms(1) have search_for_correct_label_for_q_and_chs:
    "GOTO_on_List_Prog \<turnstile>\<^sub>l
     (pc_start + 2, s\<^sub>1) \<rightarrow>\<^bsub>index q_chs_enum_list (hd (s\<^sub>1 ST), s\<^sub>1 CHS)\<^esub>
     (pc_start + 2 + index q_chs_enum_list (hd (s\<^sub>1 ST), s\<^sub>1 CHS), s\<^sub>1)"
    using search_for_correct_label_for_q_and_chs \<open>fst cfg < Q\<close> by presburger
  from s\<^sub>1 assms(1) \<open>fst cfg < Q\<close> have jump_to_correct_label:
    "GOTO_on_List_Prog \<turnstile>\<^sub>l
     (pc_start + 2 + index q_chs_enum_list (hd (s\<^sub>1 ST), s\<^sub>1 CHS), s\<^sub>1) \<rightarrow>
     (label_of_block_for_q_chs (hd (s\<^sub>1 ST), s\<^sub>1 CHS), s\<^sub>1)"
    using jump_to_correct_label by presburger
  from s\<^sub>1 assms(1-2) \<open>exe M cfg = cfg'\<close> obtain s\<^sub>2 where block_for_q_chs_correct:
    "GOTO_on_List_Prog \<turnstile>\<^sub>l
     (label_of_block_for_q_chs (hd (s\<^sub>1 ST), s\<^sub>1 CHS), s\<^sub>1) \<rightarrow>\<^bsub>block_for_q_chs_len - 1\<^esub>
     (label_of_block_for_q_chs (hd (s\<^sub>1 ST), s\<^sub>1 CHS) + block_for_q_chs_len - 1, s\<^sub>2)"
    and "s\<^sub>2 \<sim> cfg'"
    using block_for_q_chs_correct [where ?s = s\<^sub>1 and ?cfg = cfg and ?cfg' = cfg']
    by blast
  from assms(1) \<open>fst cfg < Q\<close> s\<^sub>1 have jump_back_to_begin:
    "GOTO_on_List_Prog \<turnstile>\<^sub>l
     (label_of_block_for_q_chs (hd (s\<^sub>1 ST), s\<^sub>1 CHS) + block_for_q_chs_len - 1, s\<^sub>2) \<rightarrow>
     (pc_start, s\<^sub>2)"
    using jump_back_to_begin by blast

  from read_state_and_chars_correct search_for_correct_label_for_q_and_chs
  have "GOTO_on_List_Prog \<turnstile>\<^sub>l (pc_start, s)
        \<rightarrow>\<^bsub>2 + index q_chs_enum_list (hd (s\<^sub>1 ST), s\<^sub>1 CHS)\<^esub>
        (pc_start + 2 + index q_chs_enum_list (hd (s\<^sub>1 ST), s\<^sub>1 CHS), s\<^sub>1)"
    by blast
  moreover
  have "(hd (s\<^sub>1 ST), s\<^sub>1 CHS) \<in> set q_chs_enum_list"
  proof -
    from \<open>s\<^sub>1 \<sim> cfg\<close> \<open>fst cfg < Q\<close> \<open>wf_cfg cfg\<close> have "hd (s\<^sub>1 ST) < Q"
      by (simp add: configuration_of_prog_same_to_TM_D(1))
    
    from s\<^sub>1 \<open>s\<^sub>1 \<sim> cfg\<close> \<open>wf_cfg cfg\<close> have "\<forall>k<K. s\<^sub>1 CHS ! k < G"
      by (simp add: wf_cfg_D(3) wf_cfg_D(4))
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
    "GOTO_on_List_Prog \<turnstile>\<^sub>l (pc_start, s) \<rightarrow>\<^bsub>t_entrance\<^esub>
     (pc_start + 2 + index q_chs_enum_list (hd (s\<^sub>1 ST), s\<^sub>1 CHS), s\<^sub>1)"
    using entrance_block_length
    by (metis (no_types, lifting) add_2_eq_Suc add_2_eq_Suc' less_or_eq_imp_le nat_add_left_cancel_le)
  with jump_to_correct_label
  have "GOTO_on_List_Prog \<turnstile>\<^sub>l (pc_start, s) \<rightarrow>\<^bsub>t_entrance + 1\<^esub>
        (label_of_block_for_q_chs (hd (s\<^sub>1 ST), s\<^sub>1 CHS), s\<^sub>1)"
    by auto        
  with block_for_q_chs_correct
  have "GOTO_on_List_Prog \<turnstile>\<^sub>l (pc_start, s)
        \<rightarrow>\<^bsub>t_entrance + 1 + (block_for_q_chs_len - 1)\<^esub>
        (label_of_block_for_q_chs (hd (s\<^sub>1 ST), s\<^sub>1 CHS) + block_for_q_chs_len - 1, s\<^sub>2)"
    by blast
  moreover
  have "block_for_q_chs_len > 1" by simp
  ultimately
  have "GOTO_on_List_Prog \<turnstile>\<^sub>l (pc_start, s)
        \<rightarrow>\<^bsub>t_entrance + block_for_q_chs_len\<^esub>
        (label_of_block_for_q_chs (hd (s\<^sub>1 ST), s\<^sub>1 CHS) + block_for_q_chs_len - 1, s\<^sub>2)"
    by (simp add: exec1\<^sub>l_exec\<^sub>l_t_1)
  with jump_back_to_begin
  have "GOTO_on_List_Prog \<turnstile>\<^sub>l (pc_start, s)
        \<rightarrow>\<^bsub>t_entrance + block_for_q_chs_len + 1\<^esub>
        (pc_start, s\<^sub>2)"
    by auto

  with \<open>t_entrance \<le> entrance_block_len\<close>
  have "\<exists>t_entrance \<le> entrance_block_len.
         GOTO_on_List_Prog \<turnstile>\<^sub>l  (pc_start, s)
         \<rightarrow>\<^bsub>t_entrance + block_for_q_chs_len + 1\<^esub>
         (pc_start, s\<^sub>2)"
    by (smt (verit) Suc_eq_plus1 add_2_eq_Suc' add_Suc_right add_Suc_shift)
  with \<open>s\<^sub>2 \<sim> cfg'\<close>
  show thesis using that by presburger
qed

lemma TM_to_GOTO_on_List_correct_and_in_linear_time':
  assumes "s = config_to_state cfg"
      and "\<exists>t. execute M (0, TPS) t = cfg"
      and "fst cfg < Q"
      and "execute M cfg t = cfg'"
    shows "\<exists>s'. (s' \<sim> cfg') \<and>
          (\<exists>t' \<le> (entrance_block_len + block_for_q_chs_len + 1) * t.
           GOTO_on_List_Prog \<turnstile>\<^sub>l (pc_start, s) \<rightarrow>\<^bsub>t'\<^esub> (pc_start, s'))"
  using assms
proof (induction t arbitrary: cfg')
  case 0
  then show ?case by auto
next
  case (Suc t)
  from wf_cfg_preserved_by_execute assms(2) have "wf_cfg cfg" by blast
  from \<open>execute M cfg (Suc t) = cfg'\<close> obtain cfg_mid where cfg_mid:
    "execute M cfg t = cfg_mid" "exe M cfg_mid = cfg'"
    by auto
  with assms(2) have cfg_mid_from_0_TPS: "\<exists>t. execute M (0, TPS) t = cfg_mid"
    using execute_additive by blast
  with cfg_mid Suc.IH assms obtain t' s_mid where
    t': "t' \<le> (entrance_block_len + block_for_q_chs_len + 1) * t" and
    s_mid: "GOTO_on_List_Prog \<turnstile>\<^sub>l (pc_start, s) \<rightarrow>\<^bsub>t'\<^esub> (pc_start, s_mid)" "s_mid \<sim> cfg_mid"
    by auto
  show ?case
  proof (cases "fst cfg_mid < Q")
    case True
    with \<open>exe M cfg_mid = cfg'\<close> cfg_mid_from_0_TPS \<open>s_mid \<sim> cfg_mid\<close>
    obtain s' where
      "\<exists>t_entrance\<le>entrance_block_len.
        GOTO_on_List_Prog
        \<turnstile>\<^sub>l (pc_start, s_mid) \<rightarrow>\<^bsub>t_entrance + block_for_q_chs_len + 1\<^esub> (pc_start, s')"
      "s' \<sim> cfg'"
      using TM_to_GOTO_on_List_correct_for_single_step
      by blast
    then obtain t_last_step where
      t_last_step: "t_last_step \<le> entrance_block_len + block_for_q_chs_len + 1" and
      s': "GOTO_on_List_Prog \<turnstile>\<^sub>l (pc_start, s_mid) \<rightarrow>\<^bsub>t_last_step\<^esub> (pc_start, s')"
      by (meson add_le_mono1)

    with s_mid have "GOTO_on_List_Prog \<turnstile>\<^sub>l (pc_start, s) \<rightarrow>\<^bsub>t' + t_last_step\<^esub> (pc_start, s')"
      by blast
    moreover
    from t' t_last_step have "t' + t_last_step \<le> (entrance_block_len + block_for_q_chs_len + 1) * (Suc t)"
      by force
    ultimately
    show ?thesis using \<open>s' \<sim> cfg'\<close> by blast
  next
    case False
    with \<open>exe M cfg_mid = cfg'\<close> Q have "cfg_mid = cfg'"
      by (simp add: exe_ge_length)
    moreover
    from t' s_mid
    have "t' \<le> (entrance_block_len + block_for_q_chs_len + 1) * Suc t \<and>
          GOTO_on_List_Prog \<turnstile>\<^sub>l (pc_start, s) \<rightarrow>\<^bsub>t'\<^esub> (pc_start, s_mid)"
      by auto
    ultimately
    show ?thesis
      using s_mid by blast 
  qed
qed


theorem TM_to_GOTO_on_List_correct_and_in_linear_time:
  obtains s
    where "\<exists>t \<le> T. \<exists>c. \<exists>t' \<le> c * t + 1.
          (GOTO_on_List_Prog \<turnstile>\<^sub>l (pc_start, s\<^sub>0) \<rightarrow>\<^bsub>t'\<^esub> (pc_halt, s))"
      and "s \<sim> (Q, TPS')"
proof -
  from runtime_M obtain t where execute_M: "execute M (0, TPS) t = (Q, TPS')" and t: "t \<le> T"
    using Q unfolding transforms_def transits_def
    by blast
  then obtain s t' where
    "s \<sim> (Q, TPS')"
    "t' \<le> (entrance_block_len + block_for_q_chs_len + 1) * t"
    "GOTO_on_List_Prog \<turnstile>\<^sub>l (pc_start, s\<^sub>0) \<rightarrow>\<^bsub>t'\<^esub> (pc_start, s)"
  proof (cases "Q = 0")
    case True
    with execute_M Q have "TPS' = TPS"
      by (metis execute.simps(1) fst_conv halting_config_execute old.prod.inject) 
    with \<open>Q = 0\<close> have "s\<^sub>0 \<sim> (Q, TPS')" by auto
    moreover
    have "GOTO_on_List_Prog \<turnstile>\<^sub>l (pc_start, s\<^sub>0) \<rightarrow>\<^bsub>0\<^esub> (pc_start, s\<^sub>0)"
         "0 \<le> (entrance_block_len + block_for_q_chs_len + 1) * t"
      by auto
    ultimately
    show ?thesis using that by blast 
  next
    case False
    let ?cfg = "(0, TPS)"
    from \<open>Q \<noteq> 0\<close> have "fst ?cfg < Q" by simp
    moreover
    have "execute M (0, TPS) 0 = (0, TPS)" by simp
    ultimately
    show ?thesis
      using execute_M
      using TM_to_GOTO_on_List_correct_and_in_linear_time'
            [where ?cfg = ?cfg and ?s = s\<^sub>0 and ?t = t and ?cfg' = "(Q, TPS')"]
      using that by blast
  qed
  moreover
  value "GOTO_on_List_Prog !! pc_start"
  from \<open>s \<sim> (Q, TPS')\<close> have "s ST = [Q]"
    by (simp add: configuration_of_prog_same_to_TM_D(1)) 
  then have  "GOTO_on_List_Prog \<turnstile>\<^sub>l (pc_start, s) \<rightarrow> (pc_halt, s)"
    by fastforce
  ultimately
  have "\<exists>t' \<le> (entrance_block_len + block_for_q_chs_len + 1) * t + 1.
        GOTO_on_List_Prog \<turnstile>\<^sub>l (pc_start, s\<^sub>0) \<rightarrow>\<^bsub>t'\<^esub> (pc_halt, s)"
    by fastforce
  then have "\<exists>c. \<exists>t' \<le> c * t + 1. GOTO_on_List_Prog \<turnstile>\<^sub>l (pc_start, s\<^sub>0) \<rightarrow>\<^bsub>t'\<^esub> (pc_halt, s)"
    by fast
  with t have "\<exists>t \<le> T. \<exists>c. \<exists>t' \<le> c * t + 1. GOTO_on_List_Prog \<turnstile>\<^sub>l (pc_start, s\<^sub>0) \<rightarrow>\<^bsub>t'\<^esub> (pc_halt, s)"
    by blast
  with \<open>s \<sim> (Q, TPS')\<close> show thesis
    using that by blast
qed

end
end