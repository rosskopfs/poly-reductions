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
  sorry

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


definition tm_minus' :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_minus' j1 j2 \<equiv> cartesian (tm_minus j1 j2) 4"


definition tm_sub :: "tapeidx \<Rightarrow> tapeidx \<Rightarrow> machine" where
  "tm_sub j1 j2 \<equiv>
    tm_minus' j1 j2 ;;
    tm_lconst_until j2 j2 {h. h \<noteq> \<zero> \<and> h \<noteq> \<box>} \<box> ;;
    tm_cr j1 ;;
    tm_cr j2"

end