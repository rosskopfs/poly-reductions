theory TM_to_GOTO_on_List
  imports GOTO_on_List "IMPminus_TM-Def.Global_Defs" Cook_Levin.Basics
begin

locale TM_to_GOTO_on_List =
    fixes M :: machine
      and K :: nat \<comment>\<open>K: number of tapes\<close>
      and G :: nat \<comment>\<open>G: size of tape character set\<close>
  assumes TM: "turing_machine K G M"

    fixes Q :: nat \<comment>\<open>Q: number of states, halting state excluded\<close>
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

fun s\<^sub>0 :: state\<^sub>l where          
  "s\<^sub>0 (TP n) = tape_content_to_list (TPS ::: n) MAX_LEN" |
  "s\<^sub>0 ST = [0]" |
  "s\<^sub>0 (HP n) = [TPS :#: n]" |
  "s\<^sub>0 (TMP n) = []"

subsection \<open>Definition of the transform function\<close>

value "List.product [0..<5] (product_lists (replicate 4 [0..1]))"

fun entrance_block_gen :: "(state \<times> symbol list) list \<Rightarrow> nat \<Rightarrow> GOTO\<^sub>l_prog" where
  "entrance_block_gen [] _ = [
     IF ST = L [Q] THEN GOTO\<^sub>l pc_halt,
     TMP 0 ::=\<^sub>l ReadChs [0..<K]]" |
  "entrance_block_gen ((q, chs) # q_chs_s) idx =
    entrance_block_gen q_chs_s (Suc idx) @ [
    IF ST = L [q] AND TMP 0 = L chs
    THEN GOTO\<^sub>l ((Suc (Suc (Q * G ^ MAX_LEN))) + idx * (Suc (3 * K)))]"

lemma entrance_block_gen_length: "length (entrance_block_gen q_xs_s n) = Suc (Suc (length q_xs_s))"
  by (induction q_xs_s arbitrary: n) auto

definition entrance_block :: "GOTO\<^sub>l_prog" where
  "entrance_block =
   entrance_block_gen (List.product [0..<Q] (product_lists (replicate MAX_LEN [0..<G]))) 0"

lemma entrance_block_length: "length entrance_block = Suc (Suc (Q * G ^ MAX_LEN))"
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
  have "length (product_lists (replicate MAX_LEN [0..<G])) = G ^ MAX_LEN"
    using length_product_lists [of "replicate MAX_LEN [0..<G]"]
    by simp
  then have "length (List.product [0..<Q] (product_lists (replicate MAX_LEN [0..<G]))) =
             Q * G ^ MAX_LEN"
    by auto
  then show ?thesis
    unfolding entrance_block_def
    using entrance_block_gen_length
    by fastforce
qed

fun block_for_q_and_chs :: "state \<times> action list \<Rightarrow> GOTO\<^sub>l_prog" where
  "block_for_q_and_chs q_act_s =
     (ST ::=\<^sub>l L [[*] q_act_s]) # \<comment> \<open>update state\<close>
     (concat (map (\<lambda>n. [
        TapeModify n (q_act_s [.] n), \<comment> \<open>tape modification\<close>
        case q_act_s [~] n of
          Left \<Rightarrow> MoveLeft n | Right \<Rightarrow> MoveRight n | Stay \<Rightarrow> NOP\<^sub>l, \<comment> \<open>head movement\<close>
        GOTO\<^sub>l pc_start])
      [0..<K]))" \<comment> \<open>for each tape\<close>

lemma length_block_for_q_and_chs: "length (block_for_q_and_chs q_act_s) = Suc (3 * K)"
proof -
  let ?f = "(\<lambda>n. [
    TapeModify n (q_act_s [.] n), \<comment> \<open>tape modification\<close>
    case q_act_s [~] n of
      Left \<Rightarrow> MoveLeft n | Right \<Rightarrow> MoveRight n | Stay \<Rightarrow> NOP\<^sub>l, \<comment> \<open>head movement\<close>
    GOTO\<^sub>l pc_start])"
  have "length (?f n) = 3" for n by auto
  then have "map length (map ?f [0..<K]) = replicate K 3"
    by (simp add: comp_def map_replicate_trivial)
  moreover
  have "sum_list (replicate K 3) = 3 * K"
    by (simp add: sum_list_replicate)
  ultimately
  have "length (concat (map ?f [0..<K])) = 3 * K"
    by (simp add: length_concat)
  then show ?thesis by auto
qed

definition blocks_for_actions :: "GOTO\<^sub>l_prog" where
  "blocks_for_actions =
   concat (map (\<lambda>(q, chs). block_for_q_and_chs ((M!q) chs))
               (List.product [0..<Q] (product_lists (replicate MAX_LEN [0..<G]))))"


definition GOTO_on_List_Prog :: "GOTO\<^sub>l_prog" where
  "GOTO_on_List_Prog = HALT\<^sub>l # entrance_block @ blocks_for_actions @ [HALT\<^sub>l]"

subsection \<open>Correctness of the transform function\<close>

theorem TM_to_GOTO_on_List_correct:
  assumes "GOTO_on_List_Prog \<turnstile>\<^sub>l (1, s\<^sub>0) \<rightarrow>* (0, s)"
    shows "\<forall>k < K. \<forall>p < MAX_LEN. (s (TP k)) ! p = (TPS':::k) p"
  sorry

subsection \<open>Runtime of the transformed program\<close>

theorem TM_to_GOTO_on_List_in_linear_time:
  "\<exists>c. (GOTO_on_List_Prog \<turnstile>\<^sub>l (pc, s) \<rightarrow>\<^bsub>(c * T)\<^esub> (0, s))"
  sorry

end

end