theory TM_to_GOTO_on_List
  imports GOTO_on_List "IMPminus_TM-Def.Global_Defs" Cook_Levin.Basics
begin

locale TM_to_GOTO_on_List =
    fixes M :: machine
      and K :: nat \<comment>\<open>K: number of tapes\<close>
      and G :: nat \<comment>\<open>G: size of tape character set\<close>
  assumes TM: "turing_machine K G M"

    fixes TPS :: "tape list"  \<comment>\<open>TPS: input tapes\<close>
      and T :: nat            \<comment>\<open>T: runtime\<close>
      and TPS' :: "tape list" \<comment>\<open>TPS': output tapes\<close>
  assumes runtime_M: "transforms M TPS T TPS'"

    fixes MAX_LEN :: nat    \<comment>\<open>maximum length of all tapes during the execution of the TM\<close>
begin

definition "Q = length M" \<comment>\<open>Q: number of states, halting state excluded\<close>

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

fun entrance_block_gen :: "(state \<times> symbol list) list \<Rightarrow> pc \<Rightarrow> GOTO\<^sub>l_prog" where
  "entrance_block_gen [] pc = [
    IF ST = L [Q] THEN GOTO\<^sub>l pc,
    TMP 0 ::=\<^sub>l ReadChs [0..<K]]" | (*TODO: replace pc with the label of M_end*)
  "entrance_block_gen ((q, chs) # q_chs_s) pc =
    entrance_block_gen q_chs_s (Suc pc) @ [
    IF ST = L [q] AND TMP 0 = L chs THEN GOTO\<^sub>l pc]" (*TODO: replace pc with the label of M_q_chs*)

definition entrance_block :: "GOTO\<^sub>l_prog" where
  "entrance_block =
   entrance_block_gen (List.product [0..<Q] (product_lists (replicate MAX_LEN [0..<G]))) 0"

fun block_for_q_and_chs :: "state \<times> action list \<Rightarrow> GOTO\<^sub>l_prog" where
  "block_for_q_and_chs q_act_s = [
    ST ::=\<^sub>l L [[*] q_act_s]] @
     (concat (map (\<lambda>n. [
        TapeModify n (q_act_s [.] n),
        case q_act_s [~] n of
          Left \<Rightarrow> MoveLeft n |
          Right \<Rightarrow> MoveRight n |
          Stay \<Rightarrow> NOP\<^sub>l,
        GOTO\<^sub>l 0])
      [0..<K]))"

definition blocks_for_actions :: "GOTO\<^sub>l_prog" where
  "blocks_for_actions =
   concat (map (\<lambda>(q, chs). block_for_q_and_chs ((M!q) chs))
               (List.product [0..<Q] (product_lists (replicate MAX_LEN [0..<G]))))"


definition GOTO_on_List_Prog :: "GOTO\<^sub>l_prog" where
  "GOTO_on_List_Prog = entrance_block @ blocks_for_actions @ [HALT\<^sub>l]"

subsection \<open>Correctness of the transform function\<close>

theorem TM_to_GOTO_on_List_correct:
  assumes "GOTO_on_List_Prog \<turnstile>\<^sub>l (1, s\<^sub>0) \<rightarrow>* (0, s)"
    shows "\<forall>k < K. \<forall>p < MAX_LEN. (s (TP k)) ! p = (TPS':::k) p"
  sorry

subsection \<open>Runtime of the transformed program\<close>

lemma length_entrance_block_gen: "length (entrance_block_gen l n) = Suc (Suc (length l))"
  by (induction l arbitrary: n) auto

lemma "length entrance_block = Suc (Suc (Q * (MAX_LEN ^ G)))"
proof -
  have "length [0..<Q] = Q" by force
  moreover
  have "length (replicate MAX_LEN [0..<G]) = MAX_LEN" by simp
  have "length (product_lists (replicate MAX_LEN [0..<G])) = MAX_LEN ^ G"
    sorry
  have "length (List.product [0..<Q] (product_lists (replicate MAX_LEN [0..<G]))) = Q * (MAX_LEN ^ G)"
    sorry
  then show ?thesis
    unfolding entrance_block_def
    using length_entrance_block_gen
    by simp
qed

theorem TM_to_GOTO_on_List_in_linear_time:
  "\<exists>c. (GOTO_on_List_Prog \<turnstile>\<^sub>l (pc, s) \<rightarrow>\<^bsub>(c * T)\<^esub> (0, s))"
  sorry

end

end