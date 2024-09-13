theory TM_Minus
  imports "IMP_Minus.AExp" "IMP_Minus.Com" "HOL-IMP.Star" Main  
   Cook_Levin.Basics Cook_Levin.Combinations  Cook_Levin.Elementary   Cook_Levin.Arithmetic 
begin


fun carry_minus :: "symbol list \<Rightarrow> symbol list \<Rightarrow> nat \<Rightarrow> symbol" where
  "carry_minus xs ys 0 = \<triangleright>" |
  "carry_minus xs ys (Suc i) = (if (todigit (digit xs i) < todigit (digit ys i) + todigit (carry_minus xs ys i)) then \<one> else \<zero>)"

definition minusdigit :: "symbol list \<Rightarrow> symbol list \<Rightarrow> nat \<Rightarrow> symbol" where
  "minusdigit xs ys i \<equiv> tosym ((todigit (digit xs i) + todigit (digit ys i) + todigit (carry_minus xs ys i)) mod 2)"

definition cmd_minus0 :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> command" where
  "cmd_minus0 j1 j2 rs \<equiv>
    (if rs ! j1 = \<box> \<and> rs ! j2 = \<box> then (if todigit(last rs) = 1 then 1 else 2) else 0 ,
     (map (\<lambda>j.
       if j = j1 then (rs ! j, Right)
        else if j = j2 then (tosym (( 2+ todigit (rs ! j1) - todigit (rs ! j2) - todigit (last rs)) mod 2), Right)
        else if j = length rs - 1 then (tosym (if todigit (rs ! j1) < todigit (rs ! j2) + todigit (last rs) then 1 else 0), Stay)
          else (rs ! j, Stay)) [0..<length rs]))"


lemma  plus_minus_mod2_eq:"a\<ge>b\<longrightarrow> (a-b) mod (2::nat)=(a+b) mod 2"
  by (simp add: mod2_eq_if)

lemma sem_cmd_minus:
  assumes "j1 \<noteq> j2"
    and "j1 < k - 1"
    and "j2 < k - 1"
    and "j2 > 0"
    and "length tps = k"
    and "bit_symbols xs"
    and "bit_symbols ys"
    and "tps ! j1 = (\<lfloor>xs\<rfloor>, Suc t)"
    and "tps ! j2 = (\<lfloor>map (minusdigit xs ys) [0..<t] @ drop t ys\<rfloor>, Suc t)"
    and "last tps = \<lceil>carry_minus xs ys t\<rceil>"
    and "rs = read tps"
    and "c=carry_minus xs ys (Suc t)"
    and "tps' = tps
      [j1 := tps!j1 |+| 1,
       j2 := tps!j2 |:=| minusdigit xs ys t |+| 1,
       length tps - 1 := \<lceil>c\<rceil>]"
  shows "sem (cmd_minus0 j1 j2) (0, tps) = (if t < max (length xs) (length ys) then 0 else if (todigit (last rs) =1) then 1 else 2
         , tps')"
proof
  have "k \<ge> 2"
    using assms(3,4) by simp
  have rs1: "rs ! j1 = digit xs t"
    using assms(2,5,8,11) digit_def read_def contents_def by simp
  let ?zs = "map (minusdigit xs ys) [0..<t] @ drop t ys"
  have rs2: "rs ! j2 = digit ys t"
  proof (cases "t < length ys")
    case True
    then have "?zs ! t = ys ! t"
      by (simp add: nth_append)
    then show ?thesis
      using assms(3,5,9,11) digit_def read_def contents_def by simp
  next
    case False
    then have "length ?zs = t"
      by simp
    then have "\<lfloor>?zs\<rfloor> (Suc t) = \<box>"
      using False contents_def by simp
    then show ?thesis
      using digit_def read_def contents_def False assms(3,5,9,11) by simp
  qed
  have rs3: "last rs = carry_minus xs ys t"
    using `k \<ge> 2` assms onesie_read onesie_def read_def read_length tapes_at_read'
    by (metis (no_types, lifting) diff_less last_conv_nth length_greater_0_conv less_one list.size(3) not_numeral_le_zero)
  have *: "tosym ((todigit (rs ! j1) + todigit (rs ! j2) + todigit (last rs)) mod 2) =  minusdigit xs ys t"
    using rs1 rs2 rs3 minusdigit_def by simp
 
  have r:"2+ todigit (rs ! j1)> todigit (rs ! j2) - todigit (last rs)" by simp
  then have  **:"tosym ((2+ todigit (rs ! j1) - todigit (rs ! j2) - todigit (last rs)) mod 2) =minusdigit xs ys t"
  by (smt (z3) "*" add.commute diff_add_inverse2 minus_nat.diff_0 mod_add_self1 nat_1_add_1)

  have "\<not> (digit xs t = 0 \<and> digit ys t = 0)" if "t < max (length xs) (length ys)"
    using assms(6,7) digit_def that by auto
  then have 4: "\<not> (rs ! j1 = 0 \<and> rs ! j2 = 0)" if "t < max (length xs) (length ys)"
    using rs1 rs2 that by simp
  then have fst1: "fst (sem (cmd_minus0 j1 j2) (0, tps)) = fst (0, tps')" if "t < max (length xs) (length ys)"
    using that cmd_minus0_def assms(11) by (smt (verit, ccfv_threshold) fst_conv prod.sel(2) sem)

  have "digit xs t = 0 \<and> digit ys t = 0" if "t \<ge> max (length xs) (length ys)"
    using that digit_def by simp
  then have 5: "rs ! j1 = \<box> \<and> rs ! j2 = \<box>" if "t \<ge> max (length xs) (length ys)"
    using rs1 rs2 that by simp
  then have q6:"fst (sem (cmd_minus0 j1 j2) (0, tps)) = fst (if todigit(last rs) = 1 then 1 else 2,tps')" if "t \<ge> max (length xs) (length ys)"
    using that cmd_minus0_def assms(11) by (smt (verit, ccfv_threshold) fst_conv prod.sel(2) sem)
  then show q7:"fst (sem (cmd_minus0 j1 j2) (0, tps)) = fst (if t < max (length xs) (length ys) then 0 else if (todigit (last rs) =1) then 1 else 2
         , tps')"
    using fst1 not_less by fastforce
  show "snd (sem (cmd_minus0 j1 j2) (0, tps)) = snd (if t < max (length xs) (length ys) then 0 else if (todigit (last rs) =1) then 1 else 2
         , tps')"
  proof (rule snd_semI)
    show "proper_command k (cmd_minus0 j1 j2)"
      using cmd_minus0_def by simp
    show "length tps = k"
      using assms(5) .
    show "length tps' = k"
     by (simp add: assms(4,5,13))
    have len: "length (read tps) = k"
      by (simp add: assms read_length)
    show "act (cmd_minus0 j1 j2 (read tps) [!] j) (tps ! j) = tps' ! j"
      if "j < k" for j
    proof -
      have j: "j < length tps"
        using len that assms(5) by simp
      consider
          "j = j1"
        | "j \<noteq> j1 \<and> j = j2"
        | "j \<noteq> j1 \<and> j \<noteq> j2 \<and> j = length rs - 1"
        | "j \<noteq> j1 \<and> j \<noteq> j2 \<and> j \<noteq> length rs - 1"
        by auto
      then show ?thesis
      proof (cases)
        case 1
        then have "cmd_minus0 j1 j2 (read tps) [!] j = (read tps ! j, Right)"
          using that len cmd_minus0_def by simp
        then have "act (cmd_minus0 j1 j2 (read tps) [!] j) (tps ! j) = tps ! j |+| 1"
          using act_Right[OF j] by simp
        moreover have "tps' ! j = tps ! j |+| 1"
          using assms(1,2,5,6,12,13) that 1 by simp
        ultimately show ?thesis
          by force
      next
        case 2
        then have "cmd_minus0 j1 j2 (read tps) [!] j =
            (tosym ((todigit (rs ! j1) + todigit (rs ! j2) + todigit (last rs)) mod 2), Right)"
          using that len cmd_minus0_def assms(11) by simp
        then have "cmd_minus0 j1 j2 (read tps) [!] j = (minusdigit xs ys t, Right)"
          using * by simp
        moreover have "tps' ! j2 = tps!j2 |:=| minusdigit xs ys t |+| 1"
          using assms(3,4,5,6,12,13) by simp
        ultimately show ?thesis
          using act_Right' 2 by simp
      next
        case 3
        then have "cmd_minus0 j1 j2 (read tps) [!] j =(if (todigit (rs ! j1) < todigit  (rs ! j2) + todigit (last rs)) then \<one> else \<zero>, Stay)"
          using that len cmd_minus0_def assms(11) by simp
        then have "cmd_minus0 j1 j2 (read tps) [!] j = (carry_minus xs ys (Suc t), Stay)"
          using rs1 rs2 rs3 by simp
        moreover have "tps' ! (length tps - 1) = \<lceil>c\<rceil>"
          using 3 assms(5,6,11,12,13) len that by simp
        ultimately show ?thesis
          using 3 act_onesie assms(3,4,5,6,10,11,12) len 
          by (metis add_diff_inverse_nat last_length less_nat_zero_code nat_diff_split_asm plus_1_eq_Suc)
      next
        case 4
        then have "cmd_minus0 j1 j2 (read tps) [!] j = (read tps ! j, Stay)"
          using that len cmd_minus0_def assms(11) by simp
        then have "act (cmd_minus0 j1 j2 (read tps) [!] j) (tps ! j) = tps ! j"
          using act_Stay[OF j] by simp
        moreover have "tps' ! j = tps ! j"
          using that 4 len assms(5,6,11,12,13) by simp
        ultimately show ?thesis
          by simp
      qed
    qed
  qed
qed

corollary sem_cmd_minus0':
  assumes "j1 \<noteq> j2"
    and "j1 < k - 1"
    and "j2 < k - 1"
    and "j2 > 0"
    and "length tps = k"
    and "bit_symbols xs"
    and "bit_symbols ys"
    and "tps ! j1 = (\<lfloor>xs\<rfloor>, Suc t)"
    and "tps ! j2 = (\<lfloor>map (minusdigit xs ys) [0..<t] @ drop t ys\<rfloor>, Suc t)"
    and "last tps = \<lceil>carry_minus xs ys t\<rceil>"
     and "rs = read tps"
    and "c=carry_minus xs ys (Suc t)"
    and "tps' = tps
      [j1 := (\<lfloor>xs\<rfloor>, Suc (Suc t)),
       j2 := (\<lfloor>map (minusdigit xs ys) [0..<Suc t] @ drop (Suc t) ys\<rfloor>, Suc (Suc t)),
       length tps - 1 := \<lceil>c\<rceil>]"
  shows "sem (cmd_minus0 j1 j2) (0, tps) = (if Suc t \<le> max (length xs) (length ys) then 0 else if (todigit (last rs) =1) then 1 else 2
         , tps')"
proof -
  have "tps ! j1 |+| 1 = (\<lfloor>xs\<rfloor>, Suc (Suc t))"
    using assms(8) by simp
  moreover have "tps ! j2 |:=| minusdigit xs ys t |+| 1 =
      (\<lfloor>map (minusdigit xs ys) [0..<Suc t] @ drop (Suc t) ys\<rfloor>, Suc (Suc t))"
    using contents_map_append_drop assms(8,9,10,11) by simp
  ultimately show ?thesis
    using sem_cmd_minus[OF assms(1-10)] assms(11,12,13) less_eq_Suc_le by presburger
qed

definition tm_minus :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_minus j1 j2 \<equiv> [cmd_minus0 j1 j2,(cmd_ltrans_until 0 j2 {\<triangleright>} (\<lambda>x. \<box>))]"


lemma turing_command_cmd_ltrans_until:"j2 > 0\<longrightarrow>k\<ge>2 \<longrightarrow> G\<ge>4 \<longrightarrow>turing_command k 2 G (cmd_ltrans_until 0 j2 {\<triangleright>} (\<lambda>x. \<box>))"
  unfolding  cmd_ltrans_until_def using  turing_machine_def by auto

lemma tm_minus_tm:
  assumes "j2 > 0" and "k \<ge> 2" and "G \<ge> 4"
  shows "turing_machine k G (tm_minus j1 j2)"
  unfolding tm_minus_def cmd_ltrans_until_def using assms(1-3) cmd_minus0_def turing_machine_def  turing_command_cmd_ltrans_until
  by auto

lemma tm_minus_immobile:
  fixes k :: nat
  assumes "j1 < k" and "j2 < k"
  shows "immobile (tm_minus j1 j2) k (Suc k)"
proof -
  let ?M = "tm_minus j1 j2"
  { fix q :: nat and rs :: "symbol list"
    assume q: "q < length ?M"
    assume rs: "length rs = Suc k"
    then have len: "length rs - 1 = k"
      by simp
    have neq: "k \<noteq> j1" "k \<noteq> j2"
      using assms by simp_all
    have M_0:"?M ! 0 = cmd_minus0 j1 j2"
      using tm_minus_def q by simp
     have M_1:"?M ! 1= (cmd_ltrans_until 0 j2 {\<triangleright>} (\<lambda>x. \<box>))"
       using tm_minus_def q by auto
     have "(cmd_ltrans_until 0 j2 {\<triangleright>} (\<lambda>x. \<box>)) rs [!] k =
        (rs!k,Stay)"
       unfolding  cmd_ltrans_until_def using cmd_ltrans_until_def rs len neq 
       by (smt (verit) add_0 assms(2) diff_zero length_upt lessI less_nat_zero_code nth_map nth_upt snd_conv)
     have "(cmd_ltrans_until 0 j2 {\<triangleright>} (\<lambda>x. \<box>)) rs [!] k =
        (rs!k,Stay)"
       unfolding  cmd_ltrans_until_def using cmd_ltrans_until_def rs len neq 
     by (smt (verit) add_0 assms(2) diff_zero length_upt lessI less_nat_zero_code nth_map nth_upt snd_conv)
     then have ee:"(cmd_ltrans_until 0 j2 {\<triangleright>} (\<lambda>x. \<box>)) rs [~] k =
        Stay" by auto
  
   moreover have "(cmd_minus0 j1 j2) rs [!] k =
        (tosym (if todigit (rs ! j1) < todigit (rs ! j2) + todigit (last rs) then 1 else 0), Stay)"
      using cmd_minus0_def rs len neq by fastforce
    then have "(cmd_minus0 j1 j2) rs [~] k = Stay\<and> (cmd_ltrans_until 0 j2 {\<triangleright>} (\<lambda>x. \<box>)) rs [~] k =
        Stay" using ee by simp
    then  have "((tm_minus j1 j2)!0) rs [~] k = Stay\<and> ((tm_minus j1 j2)!1) rs [~] k = Stay" using M_0 M_1 by simp
    moreover have "length (tm_minus j1 j2)=2"unfolding tm_minus_def by auto
    ultimately have "\<forall>l<length (tm_minus j1 j2). ((tm_minus j1 j2)!l) rs [~] k = Stay" 
    using One_nat_def less_2_cases_iff by presburger
  }
  then show ?thesis unfolding immobile_def by blast
qed

(* TODO *)
lemma execute_tm_minus:
  assumes "j1 \<noteq> j2"
    and "j1 < k - 1"
    and "j2 < k - 1"
    and "j2 > 0"
    and "length tps = k"
    and "bit_symbols xs"
    and "bit_symbols ys"
    and "t \<le> Suc (max (length xs) (length ys))"
    and "tps ! j1 = (\<lfloor>xs\<rfloor>, 1)"
    and "tps ! j2 = (\<lfloor>ys\<rfloor>, 1)"
    and "last tps = \<lceil>\<triangleright>\<rceil>"
  shows "execute (tm_minus j1 j2) (0, tps) t =
    (if t \<le> max (length xs) (length ys) then 0 else 1, tps
      [j1 := (\<lfloor>xs\<rfloor>, Suc t),
       j2 := (\<lfloor>map (minusdigit xs ys) [0..<t] @ drop t ys\<rfloor>, Suc t),
       length tps - 1 := \<lceil>carry_minus xs ys t\<rceil>])"
  using assms(8)
proof (induction t)
  case 0
  have "carry xs ys 0 = 1"
    by simp
  moreover have "map (sumdigit xs ys) [0..<0] @ drop 0 ys = ys"
    by simp
  ultimately have "tps = tps
      [j1 := (\<lfloor>xs\<rfloor>, Suc 0),
       j2 := (\<lfloor>map (sumdigit xs ys) [0..<0] @ drop 0 ys\<rfloor>, Suc 0),
       length tps - 1 := \<lceil>carry xs ys 0\<rceil>]"
    using assms
    by (metis One_nat_def add_diff_inverse_nat last_length less_nat_zero_code
      list_update_id nat_diff_split_asm plus_1_eq_Suc)
  then show ?case
    by simp
next
  case (Suc t)
  let ?M = "tm_plus j1 j2"
  have "execute ?M (0, tps) (Suc t) = exe ?M (execute ?M (0, tps) t)"
      (is "_ = exe ?M ?cfg")
    by simp
  also have "... = sem (cmd_plus j1 j2) ?cfg"
    using Suc tm_plus_def exe_lt_length by simp
  also have "... = (if Suc t \<le> max (length xs) (length ys) then 0 else 1, tps
      [j1 := (\<lfloor>xs\<rfloor>, Suc (Suc t)),
       j2 := (\<lfloor>map (sumdigit xs ys) [0..<Suc t] @ drop (Suc t) ys\<rfloor>, Suc (Suc t)),
       length tps - 1 := \<lceil>carry xs ys (Suc t)\<rceil>])"
  proof -
    let ?tps = "tps
      [j1 := (\<lfloor>xs\<rfloor>, Suc t),
       j2 := (\<lfloor>map (sumdigit xs ys) [0..<t] @ drop t ys\<rfloor>, Suc t),
       length tps - 1 := \<lceil>carry xs ys t\<rceil>]"
    let ?tps' = "?tps
      [j1 := (\<lfloor>xs\<rfloor>, Suc (Suc t)),
       j2 := (\<lfloor>map (sumdigit xs ys) [0..<Suc t] @ drop (Suc t) ys\<rfloor>, Suc (Suc t)),
       length tps - 1 := \<lceil>carry xs ys (Suc t)\<rceil>]"
    have cfg: "?cfg = (0, ?tps)"
      using Suc by simp
    have tps_k: "length ?tps = k"
      using assms(2,3,5) by simp
    have tps_j1: "?tps ! j1 = (\<lfloor>xs\<rfloor>, Suc t)"
      using assms(1-3,5) by simp
    have tps_j2: "?tps ! j2 = (\<lfloor>map (sumdigit xs ys) [0..<t] @ drop t ys\<rfloor>, Suc t)"
      using assms(1-3,5) by simp
    have tps_last: "last ?tps = \<lceil>carry xs ys t\<rceil>"
      using assms
      by (metis One_nat_def carry.simps(1) diff_Suc_1 last_list_update length_list_update list_update_nonempty prod.sel(2) tps_j1)
    then have "sem (cmd_plus j1 j2) (0, ?tps) = (if Suc t \<le> max (length xs) (length ys) then 0 else 1, ?tps')"
      using sem_cmd_plus'[OF assms(1-4) tps_k assms(6,7) tps_j1 tps_j2 tps_last] assms(1-3)
      by (smt (verit, best) Suc.prems Suc_lessD assms(5) tps_k)
    then have "sem (cmd_plus j1 j2) ?cfg = (if Suc t \<le> max (length xs) (length ys) then 0 else 1, ?tps')"
      using cfg by simp
    moreover have "?tps' = tps
      [j1 := (\<lfloor>xs\<rfloor>, Suc (Suc t)),
       j2 := (\<lfloor>map (sumdigit xs ys) [0..<Suc t] @ drop (Suc t) ys\<rfloor>, Suc (Suc t)),
       length tps - 1 := \<lceil>carry xs ys (Suc t)\<rceil>]"
      using assms by (smt (z3) list_update_overwrite list_update_swap)
    ultimately show ?thesis
      by simp
  qed
  finally show ?case
    by simp
qed

lemma tm_plus_bounded_write:
  assumes "j1 < k - 1"
  shows "bounded_write (tm_plus j1 j2) (k - 1) 4"
  using assms cmd_plus_def tm_plus_def bounded_write_def by simp

lemma carry_max_length:
  assumes "bit_symbols xs" and "bit_symbols ys"
  shows "carry xs ys (Suc (max (length xs) (length ys))) = \<zero>"
proof -
  let ?t = "max (length xs) (length ys)"
  have "carry xs ys (Suc ?t) = tosym ((todigit (digit xs ?t) + todigit (digit ys ?t) + todigit (carry xs ys ?t)) div 2)"
    by simp
  then have "carry xs ys (Suc ?t) = tosym (todigit (carry xs ys ?t) div 2)"
    using digit_def by simp
  moreover have "carry xs ys ?t \<le> \<one>"
    using carry_le assms by fastforce
  ultimately show ?thesis
    by simp
qed

corollary execute_tm_plus_halt:
  assumes "j1 \<noteq> j2"
    and "j1 < k - 1"
    and "j2 < k - 1"
    and "j2 > 0"
    and "length tps = k"
    and "bit_symbols xs"
    and "bit_symbols ys"
    and "t = Suc (max (length xs) (length ys))"
    and "tps ! j1 = (\<lfloor>xs\<rfloor>, 1)"
    and "tps ! j2 = (\<lfloor>ys\<rfloor>, 1)"
    and "last tps = \<lceil>\<triangleright>\<rceil>"
  shows "execute (tm_plus j1 j2) (0, tps) t =
    (1, tps
      [j1 := (\<lfloor>xs\<rfloor>, Suc t),
       j2 := (\<lfloor>map (sumdigit xs ys) [0..<t]\<rfloor>, Suc t),
       length tps - 1 := \<lceil>\<zero>\<rceil>])"
proof -
  have "execute (tm_plus j1 j2) (0, tps) t =
    (1, tps
      [j1 := (\<lfloor>xs\<rfloor>, Suc t),
       j2 := (\<lfloor>map (sumdigit xs ys) [0..<t] @ drop t ys\<rfloor>, Suc t),
       length tps - 1 := \<lceil>carry xs ys t\<rceil>])"
    using assms(8) execute_tm_plus[OF assms(1-7) _ assms(9-11)] Suc_leI Suc_n_not_le_n lessI
    by presburger
  then have "execute (tm_plus j1 j2) (0, tps) t =
    (1, tps
      [j1 := (\<lfloor>xs\<rfloor>, Suc t),
       j2 := (\<lfloor>map (sumdigit xs ys) [0..<t]\<rfloor>, Suc t),
       length tps - 1 := \<lceil>carry xs ys t\<rceil>])"
    using assms(8) by simp
  then show "execute (tm_plus j1 j2) (0, tps) t =
    (1, tps
      [j1 := (\<lfloor>xs\<rfloor>, Suc t),
       j2 := (\<lfloor>map (sumdigit xs ys) [0..<t]\<rfloor>, Suc t),
       length tps - 1 := \<lceil>\<zero>\<rceil>])"
    using assms(8) carry_max_length[OF assms(6,7)] by metis
qed

lemma transforms_tm_plusI:
  assumes "j1 \<noteq> j2"
    and "j1 < k - 1"
    and "j2 < k - 1"
    and "j2 > 0"
    and "length tps = k"
    and "bit_symbols xs"
    and "bit_symbols ys"
    and "t = Suc (max (length xs) (length ys))"
    and "tps ! j1 = (\<lfloor>xs\<rfloor>, 1)"
    and "tps ! j2 = (\<lfloor>ys\<rfloor>, 1)"
    and "last tps = \<lceil>\<triangleright>\<rceil>"
    and "tps' = tps
      [j1 := (\<lfloor>xs\<rfloor>, Suc t),
       j2 := (\<lfloor>map (sumdigit xs ys) [0..<t]\<rfloor>, Suc t),
       length tps - 1 := \<lceil>\<zero>\<rceil>]"
  shows "transforms (tm_plus j1 j2) tps t tps'"
  using assms execute_tm_plus_halt[OF assms(1-11)] tm_plus_def transforms_def transits_def
  by auto


text \<open>
The next Turing machine is the one we actually use to add two numbers. After
computing the sum by running @{const tm_plus'}, it removes trailing zeros
and performs a carriage return on the tapes $j_1$ and $j_2$.
\<close>

text \<open>
The next Turing machine removes the memorization tape from @{const tm_plus}.
\<close>

definition tm_minus' :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_minus' j1 j2 \<equiv> cartesian (tm_minus j1 j2) 4"


definition tm_sub :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_sub j1 j2 \<equiv>
    tm_minus' j1 j2 ;;
    tm_lconst_until j2 j2 {h. h \<noteq> \<zero> \<and> h \<noteq> \<box>} \<box> ;;
    tm_cr j1 ;;
    tm_cr j2"

lemma tm_minus'_tm:
  assumes "j2 > 0" and "k \<ge> 2" and "G \<ge> 4"
  shows "turing_machine k G (tm_minus' j1 j2)"
  unfolding tm_minus'_def using assms cartesian_tm tm_minus_tm by simp

lemma tm_sub_tm:
  assumes "j2 > 0" and "k \<ge> 2" and "G \<ge> 4" and "j2 < k"
  shows "turing_machine k G (tm_sub j1 j2)"
  unfolding tm_sub_def using tm_minus'_tm tm_lconst_until_tm tm_cr_tm assms by simp

locale turing_machine_add =
  fixes j1 j2 :: tapeidx
begin

definition "tm1 \<equiv> tm_minus' j1 j2"
definition "tm2 \<equiv> tm1 ;; tm_lconst_until j2 j2 {h. h \<noteq> \<zero> \<and> h \<noteq> \<box>} \<box>"
definition "tm3 \<equiv> tm2 ;; tm_cr j1"
definition "tm4 \<equiv> tm3 ;; tm_cr j2"

lemma tm4_eq_tm_add: "tm4 = tm_sub j1 j2"
  using tm4_def tm3_def tm2_def tm1_def tm_sub_def by simp

context
  fixes x y k :: nat and tps0 :: "tape list"
  assumes jk: "j1 \<noteq> j2" "j1 < k" "j2 < k" "j2 > 0" "k = length tps0"
  assumes tps0:
    "tps0 ! j1 = (\<lfloor>canrepr x\<rfloor>, 1)"
    "tps0 ! j2 = (\<lfloor>canrepr y\<rfloor>, 1)"
begin

abbreviation "xs \<equiv> canrepr x"

abbreviation "ys \<equiv> canrepr y"

lemma xs: "bit_symbols xs"
  using bit_symbols_canrepr by simp

lemma ys: "bit_symbols ys"
  using bit_symbols_canrepr by simp

abbreviation "n \<equiv> Suc (max (length xs) (length ys))"

abbreviation "m \<equiv> length (canrepr (num xs + num ys))"

definition "tps1 \<equiv> tps0
  [j1 := (\<lfloor>xs\<rfloor>, Suc n),
   j2 := (\<lfloor>map (minusdigit xs ys) [0..<n]\<rfloor>, Suc n)]"

lemma tm1 [transforms_intros]:
  assumes "ttt = n"
  shows "transforms tm1 tps0 ttt tps1"
  unfolding tm1_def
proof (tform tps: jk xs ys tps0 time: assms)
  show "tps1 = tps0
    [j1 := (\<lfloor>xs\<rfloor>, Suc ttt),
     j2 := (\<lfloor>map (minusdigit xs ys) [0..<ttt]\<rfloor>, Suc ttt)]"
    using tps1_def assms by simp
qed

definition "tps2 \<equiv> tps0
  [j1 := (\<lfloor>xs\<rfloor>, Suc n),
   j2 := (\<lfloor>canrepr (num xs + num ys)\<rfloor>, m)]"

lemma contents_canlen:
  assumes "bit_symbols zs"
  shows "\<lfloor>zs\<rfloor> (canlen zs) \<in> {h. h \<noteq> \<zero> \<and> \<box> < h}"
  using assms contents_def canlen_le_length canlen_one by auto

lemma tm2 [transforms_intros]:
  assumes "ttt = n + Suc (Suc n - canlen (map (sumdigit xs ys) [0..<n]))"
  shows "transforms tm2 tps0 ttt tps2"
  unfolding tm2_def
proof (tform tps: tps1_def jk xs ys tps0)
  let ?zs = "map (sumdigit xs ys) [0..<n]"
  have "bit_symbols ?zs"
    using sumdigit_bit_symbols by blast
  let ?ln = "Suc n - canlen ?zs"
  have "lneigh (\<lfloor>?zs\<rfloor>, Suc n) {h. h \<noteq> \<zero> \<and> \<box> < h} ?ln"
  proof (rule lneighI)
    have "\<lfloor>?zs\<rfloor> (canlen ?zs) \<in> {h. h \<noteq> \<zero> \<and> \<box> < h}"
      using contents_canlen[OF `bit_symbols ?zs`] by simp
    moreover have "Suc n - ?ln = canlen ?zs"
      by (metis One_nat_def diff_Suc_1 diff_Suc_Suc diff_diff_cancel le_imp_less_Suc
        length_map length_upt less_imp_le_nat canlen_le_length)
    ultimately have "\<lfloor>?zs\<rfloor> (Suc n - ?ln) \<in> {h. h \<noteq> \<zero> \<and> \<box> < h}"
      by simp
    then show "fst (\<lfloor>?zs\<rfloor>, Suc n) (snd (\<lfloor>?zs\<rfloor>, Suc n) - ?ln) \<in> {h. h \<noteq> \<zero> \<and> \<box> < h}"
      by simp

    have "\<lfloor>?zs\<rfloor> (Suc n - n') \<in> {\<box>, \<zero>}" if "n' < ?ln" for n'
    proof (cases "Suc n - n' \<le> n")
      case True
      moreover have 1: "Suc n - n' > 0"
        using that by simp
      ultimately have "\<lfloor>?zs\<rfloor> (Suc n - n') = ?zs ! (Suc n - n' - 1)"
        using contents_def by simp
      moreover have "Suc n - n' - 1 < length ?zs"
        using that True by simp
      moreover have "Suc n - n' - 1 \<ge> canlen ?zs"
        using that by simp
      ultimately show ?thesis
        using canlen_at_ge[of ?zs] by simp
    next
      case False
      then show ?thesis
        by simp
    qed
    then have "\<lfloor>?zs\<rfloor> (Suc n - n') \<notin> {h. h \<noteq> \<zero> \<and> \<box> < h}" if "n' < ?ln" for n'
      using that by fastforce
    then show "fst (\<lfloor>?zs\<rfloor>, Suc n) (snd (\<lfloor>?zs\<rfloor>, Suc n) - n') \<notin> {h. h \<noteq> \<zero> \<and> \<box> < h}"
        if "n' < ?ln" for n'
      using that by simp
  qed
  then show "lneigh (tps1 ! j2) {h. h \<noteq> \<zero> \<and> h \<noteq> \<box>} ?ln"
    using assms tps1_def jk by simp
  show "Suc n - canlen (map (sumdigit xs ys) [0..<n]) \<le> tps1 :#: j2"
    "Suc n - canlen (map (sumdigit xs ys) [0..<n]) \<le> tps1 :#: j2"
    using assms tps1_def jk by simp_all

  have num_zs: "num ?zs = num xs + num ys"
    using assms num_sumdigit_eq_sum'' xs ys by simp
  then have canrepr: "canrepr (num xs + num ys) = take (canlen ?zs) ?zs"
    using canrepr_take_canlen `bit_symbols ?zs` by blast
  have len_canrepr: "length (canrepr (num xs + num ys)) = canlen ?zs"
    using num_zs length_canrepr_canlen sumdigit_bit_symbols by blast

  have "lconstplant (\<lfloor>?zs\<rfloor>, Suc n) \<box> ?ln =
      (\<lfloor>canrepr (num xs + num ys)\<rfloor>, m)"
    (is "lconstplant ?tp \<box> ?ln = _")
  proof -
    have "(if Suc n - ?ln < i \<and> i \<le> Suc n then \<box> else \<lfloor>?zs\<rfloor> i) =
        \<lfloor>take (canlen ?zs) ?zs\<rfloor> i"
        (is "?lhs = ?rhs")
      for i
    proof -
      consider
          "i = 0"
        | "i > 0 \<and> i \<le> canlen ?zs"
        | "i > canlen ?zs \<and> i \<le> Suc n"
        | "i > canlen ?zs \<and> i > Suc n"
        by linarith
      then show ?thesis
      proof (cases)
        case 1
        then show ?thesis
          by simp
      next
        case 2
        then have "i \<le> Suc n - ?ln"
          using canlen_le_length
          by (metis diff_diff_cancel diff_zero le_imp_less_Suc length_map length_upt less_imp_le_nat)
        then have lhs: "?lhs = \<lfloor>?zs\<rfloor> i"
          by simp
        have "take (canlen ?zs) ?zs ! (i - 1) = ?zs ! (i - 1)"
          using 2 by (metis Suc_diff_1 Suc_less_eq le_imp_less_Suc nth_take)
        then have "?rhs = \<lfloor>?zs\<rfloor> i"
          using 2 contents_inbounds len_canrepr local.canrepr not_le canlen_le_length
          by (metis add_diff_inverse_nat add_leE)
        then show ?thesis
          using lhs by simp
      next
        case 3
        then have "Suc n - ?ln < i \<and> i \<le> Suc n"
          by (metis diff_diff_cancel less_imp_le_nat less_le_trans)
        then have "?lhs = 0"
          by simp
        moreover have "?rhs = 0"
          using 3 contents_outofbounds len_canrepr canrepr by metis
        ultimately show ?thesis
          by simp
      next
        case 4
        then have "?lhs = 0"
          by simp
        moreover have "?rhs = 0"
          using 4 contents_outofbounds len_canrepr canrepr by metis
        ultimately show ?thesis
          by simp
      qed
    qed
    then have "(\<lambda>i. if Suc n - ?ln < i \<and> i \<le> Suc n then \<box> else \<lfloor>?zs\<rfloor> i) =
        \<lfloor>canrepr (num xs + num ys)\<rfloor>"
      using canrepr by simp
    moreover have "fst ?tp = \<lfloor>?zs\<rfloor>"
      by simp
    ultimately have "(\<lambda>i. if Suc n - ?ln < i \<and> i \<le> Suc n then 0 else fst ?tp i) =
        \<lfloor>canrepr (num xs + num ys)\<rfloor>" by metis
    moreover have "Suc n - ?ln = m"
      using len_canrepr
      by (metis add_diff_inverse_nat diff_add_inverse2 diff_is_0_eq diff_zero le_imp_less_Suc length_map
        length_upt less_imp_le_nat less_numeral_extra(3) canlen_le_length zero_less_diff)
    ultimately show ?thesis
      using lconstplant[of ?tp 0 ?ln] by simp
  qed
  then show "tps2 = tps1
    [j2 := tps1 ! j2 |-| ?ln,
     j2 := lconstplant (tps1 ! j2) 0 ?ln]"
    using tps2_def tps1_def jk by simp

  show "ttt = n + Suc ?ln"
    using assms by simp
qed

definition "tps3 \<equiv> tps0
  [j1 := (\<lfloor>xs\<rfloor>, 1),
   j2 := (\<lfloor>canrepr (num xs + num ys)\<rfloor>, m)]"

lemma tm3 [transforms_intros]:
  assumes "ttt = n + Suc (Suc n - canlen (map (sumdigit xs ys) [0..<n])) + Suc n + 2"
  shows "transforms tm3 tps0 ttt tps3"
  unfolding tm3_def
proof (tform tps: tps2_def jk xs ys tps0 time: assms tps2_def jk)
  show "clean_tape (tps2 ! j1)"
    using tps2_def jk xs
    by (metis clean_tape_ncontents nth_list_update_eq nth_list_update_neq)
  show "tps3 = tps2[j1 := tps2 ! j1 |#=| 1]"
    using tps3_def tps2_def jk by (simp add: list_update_swap)
qed

definition "tps4 \<equiv> tps0
  [j1 := (\<lfloor>xs\<rfloor>, 1),
   j2 := (\<lfloor>canrepr (num xs + num ys)\<rfloor>, 1)]"

lemma tm4:
  assumes "ttt = n + Suc (Suc n - canlen (map (sumdigit xs ys) [0..<n])) + Suc n + 2 + m + 2"
  shows "transforms tm4 tps0 ttt tps4"
  unfolding tm4_def
proof (tform tps: tps3_def jk xs ys tps0 time: assms tps3_def jk)
  show "clean_tape (tps3 ! j2)"
    using tps3_def tps2_def jk tps0(1) by (metis clean_tape_ncontents list_update_id nth_list_update_eq)
  show "tps4 = tps3[j2 := tps3 ! j2 |#=| 1]"
    using tps4_def tps3_def jk by simp
qed

lemma tm4':
  assumes "ttt = 3 * max (length xs) (length ys) + 10"
  shows "transforms tm4 tps0 ttt tps4"
proof -
  let ?zs = "map (sumdigit xs ys) [0..<n]"
  have "num ?zs = num xs + num ys"
    using num_sumdigit_eq_sum'' xs ys by simp
  then have 1: "length (canrepr (num xs + num ys)) = canlen ?zs"
    using length_canrepr_canlen sumdigit_bit_symbols by blast
  moreover have "length ?zs = n"
    by simp
  ultimately have "m \<le> n"
    by (metis canlen_le_length)

  have "n + Suc (Suc n - canlen ?zs) + Suc n + 2 + m + 2 =
      n + Suc (Suc n - m) + Suc n + 2 + m + 2"
    using 1 by simp
  also have "... = n + Suc (Suc n - m) + Suc n + 4 + m"
    by simp
  also have "... = n + Suc (Suc n) - m + Suc n + 4 + m"
    using `m \<le> n` by simp
  also have "... = n + Suc (Suc n) + Suc n + 4"
    using `m \<le> n` by simp
  also have "... = 3 * n + 7"
    by simp
  also have "... = ttt"
    using assms by simp
  finally have "n + Suc (Suc n - canlen ?zs) + Suc n + 2 + m + 2 = ttt" .
  then show ?thesis
    using tm4 by simp
qed

definition "tps4' \<equiv> tps0
  [j2 := (\<lfloor>x + y\<rfloor>\<^sub>N, 1)]"

lemma tm4'':
  assumes "ttt = 3 * max (nlength x) (nlength y) + 10"
  shows "transforms tm4 tps0 ttt tps4'"
proof -
  have "canrepr (num xs + num ys) = canrepr (x + y)"
    by (simp add: canrepr)
  then show ?thesis
    using assms tps0(1) tps4'_def tps4_def tm4' by (metis list_update_id)
qed

end  (* context *)

end  (* locale *)

lemma transforms_tm_subI [transforms_intros]:
  fixes j1 j2 :: tapeidx
  fixes x y k ttt :: nat and tps tps' :: "tape list"
  assumes "j1 \<noteq> j2" "j1 < k" "j2 < k" "j2 > 0" "k = length tps"
  assumes
    "tps ! j1 = (\<lfloor>canrepr x\<rfloor>, 1)"
    "tps ! j2 = (\<lfloor>canrepr y\<rfloor>, 1)"
  assumes "ttt = 3 * max (nlength x) (nlength y) + 10"
  assumes "tps' = tps
    [j2 := (\<lfloor>x - y\<rfloor>\<^sub>N, 1)]"
  shows "transforms (tm_add j1 j2) tps ttt tps'"
proof -
  interpret loc: turing_machine_add j1 j2 .
  show ?thesis
    using loc.tm4_eq_tm_add loc.tps4'_def loc.tm4'' assms by simp
qed


end