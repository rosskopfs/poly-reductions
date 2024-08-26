theory WHILE_TM
  imports "IMP_Minus.AExp" "IMP_Minus.Com" "HOL-IMP.Star" Main  "IMP_Minus.Big_StepT"  "IMPminus_State_TM_Tape_List"
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

lemma tm_plus_tm:
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

(*
fun count_atomExp_variable ::"atomExp \<Rightarrow>vname set" where
"count_atomExp_variable (N val) ={}"| 
"count_atomExp_variable (V vname) ={vname}"

fun count_aexp_variable::"aexp \<Rightarrow>vname set" where
"count_aexp_variable (A a) =count_atomExp_variable a "|
"count_aexp_variable  (Plus a b)=(count_atomExp_variable a)\<union>(count_atomExp_variable b)" |
"count_aexp_variable  (Sub a b)=(count_atomExp_variable a)\<union>(count_atomExp_variable b)" |
"count_aexp_variable (Parity a) =count_atomExp_variable a "|
"count_aexp_variable  (RightShift a) =count_atomExp_variable a "              

fun count_com_variable::"com \<Rightarrow>vname set" where
"count_com_variable  SKIP ={}"|
"count_com_variable (Assign vname a) ={vname}\<union> (count_aexp_variable a)"|
"count_com_variable (Seq Seq1 Seq2)=(count_com_variable Seq1)\<union> (count_com_variable Seq2)"|
"count_com_variable (If vname com1 com2) = {vname}\<union> (count_com_variable com1)\<union> (count_com_variable com2)"|
"count_com_variable (While  vname com1) = {vname}\<union> (count_com_variable com1)"

(*TODO : numbering every variable from 1*) 
fun num_variable::" com \<Rightarrow> (vname \<Rightarrow> nat)" where
"num_variable com  =(\<lambda>s. 1)"

*)

(* TODO *)
fun aexpVal :: "aexp\<Rightarrow> AExp.state \<Rightarrow> val" where
"aexpVal (A a) s= (atomVal a s)"|
"aexpVal (Plus a1 a2) s= (atomVal a1 s)+(atomVal a2 s)"|
"aexpVal (Sub a1 a2) s= (atomVal a1 s)-(atomVal a2 s)"|
"aexpVal (Parity a) s = (atomVal a s) mod 2 "|
"aexpVal (RightShift a) s=(atomVal a s) div 2"

fun atomExp_TM::"(vname\<Rightarrow>nat) \<Rightarrow>atomExp \<Rightarrow> nat \<Rightarrow>machine" where
"atomExp_TM idd (N a) tp =tm_set tp (canrepr a)"|
"atomExp_TM idd (V v) tp =tm_cp_until (idd v) tp {\<box>};;tm_cr tp"

fun Aexp_TM::"(vname\<Rightarrow>nat)\<Rightarrow>aexp \<Rightarrow> machine " where
"Aexp_TM idd (A a) = (atomExp_TM idd a 2)"|
"Aexp_TM idd (Plus a1 a2) = (atomExp_TM idd a1 1) ;; ( atomExp_TM idd a2 2);;tm_cr 1;;tm_cr 2;; tm_plus 1 2"|
"Aexp_TM idd (Sub a1 a2) = (atomExp_TM idd a1 1);;(atomExp_TM idd a2 2);;tm_cr 1;;tm_cr 2;;tm_minus 1 2"|
"Aexp_TM idd (Parity a) = (atomExp_TM idd a 2);;(tm_mod2 2 2)"|
"Aexp_TM idd (RightShift a) =(atomExp_TM idd a 2);;(tm_div2 2)"

(*
TODO:read value from a tape
*)

fun tape_list_read::"nat \<Rightarrow>nat" where
" tape_list_read k = 0"
(*
fun while_TM_aux::" com\<Rightarrow>(vname\<Rightarrow>nat) \<Rightarrow>nat \<Rightarrow> machine" where
"while_TM_aux   SKIP idd k  = []"|
"while_TM_aux  (Assign v a) idd k  =  ((Aexp_TM idd a);;(tm_cp_until 2 (idd v) {\<box>}))"|
"while_TM_aux  (Seq c1 c2) idd k = ((while_TM_aux c1 idd k);;(while_TM_aux c2 idd k))"|
"while_TM_aux  (If v c1 c2) idd k =((tm_cmp 0 (idd v) 2);; IF (\<lambda>x. x!2=0) THEN (while_TM_aux c1 idd k) ELSE (while_TM_aux c1 idd k) ENDIF)"|
"while_TM_aux  (While  v c) idd k =(WHILE (tm_cmp 0 (idd v) 2) ; (\<lambda>x. x!2=0) DO while_TM_aux c idd k DONE)"
*)

fun while_TM_aux::" com\<Rightarrow> (vname\<Rightarrow>nat) \<Rightarrow> machine" where
"while_TM_aux   SKIP idd   = []"|
"while_TM_aux  (Assign v a) idd  =  (Aexp_TM idd a);;tm_cp_until 2 (idd v)  {\<box>};;(tm_erase 2)"|
"while_TM_aux  (Seq c1 c2) idd = ((while_TM_aux c1 idd);;(while_TM_aux c2 idd))"|
"while_TM_aux  (If v c1 c2) idd =((tm_cmp 0 (idd v) 2);; IF (\<lambda>x. x!2=0) THEN (while_TM_aux c1 idd) ELSE (while_TM_aux c1 idd) ENDIF)"|
"while_TM_aux  (While  v c) idd =(WHILE (tm_cmp 0 (idd v) 2) ; (\<lambda>x. x!2=0) DO while_TM_aux c idd DONE)"

fun aexp_time::"aexp\<Rightarrow>(vname\<Rightarrow>nat) \<Rightarrow>nat" where
"aexp_time (A a) s = atomVal a s "|
"aexp_time (Plus a1 a2) s = max (atomVal a1 s) (atomVal a2 s)"|
"aexp_time (Sub a1 a2) s = max (atomVal a1 s) (atomVal  a2 s)"|
"aexp_time (Parity a)  s= atomVal a s"|
"aexp_time (RightShift a) s =  atomVal a s"

inductive
  big_step_Logt :: "com \<times> AExp.state \<Rightarrow> nat \<Rightarrow> AExp.state \<Rightarrow> bool"  ("_ \<Rightarrow>\<^bsup> _ \<^esup>\<^esup> _" 55)
where
Skip: "(SKIP,s) \<Rightarrow>\<^bsup> Suc (0::nat) \<^esup>\<^esup> s"|
Assign_vname: "(x ::= a, s) \<Rightarrow>\<^bsup> Suc (aexp_time a s) \<^esup>\<^esup> s(x := aval a s)" |
Seq: "\<lbrakk> (c1,s1) \<Rightarrow>\<^bsup> x \<^esup>\<^esup> s2;  (c2,s2) \<Rightarrow>\<^bsup> y \<^esup>\<^esup> s3 ;z=x+y\<rbrakk> \<Longrightarrow> (c1;;c2, s1) \<Rightarrow>\<^bsup>z \<^esup>\<^esup> s3" |
IfTrue: "\<lbrakk> s b \<noteq> 0;  (c1,s) \<Rightarrow>\<^bsup> x \<^esup>\<^esup> t; y=x+1 \<rbrakk> \<Longrightarrow> (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup> y \<^esup>\<^esup> t" |
IfFalse: "\<lbrakk> s b = 0; (c2,s) \<Rightarrow>\<^bsup> x \<^esup>\<^esup> t; y=x+1  \<rbrakk> \<Longrightarrow> (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup> y \<^esup>\<^esup> t" |
WhileFalse: "\<lbrakk> s b = 0 \<rbrakk> \<Longrightarrow> (WHILE b \<noteq>0 DO c,s) \<Rightarrow>\<^bsup> Suc (Suc 0)\<^esup>\<^esup> s" |
WhileTrue: "\<lbrakk> s1 b \<noteq> 0;  (c,s1) \<Rightarrow>\<^bsup> x\<^esup>\<^esup> s2;  (WHILE b \<noteq>0 DO c, s2) \<Rightarrow>\<^bsup> y \<^esup>\<^esup> s3; 1+x+y=z  \<rbrakk> 
    \<Longrightarrow> (WHILE b \<noteq>0 DO c, s1) \<Rightarrow>\<^bsup> z \<^esup>\<^esup> s3" 

declare big_step_Logt.intros [intro]

text "Induction rules with pair splitting"
lemmas big_step_Logt_induct = big_step_Logt.induct[split_format(complete)]

subsection "Rule inversion"
inductive_cases Skip_tE[elim!]: "(SKIP,s) \<Rightarrow>\<^bsup> x \<^esup>\<^esup> t"
inductive_cases Assign_tE[elim!]: "(x ::= a,s) \<Rightarrow>\<^bsup> p  \<^esup>\<^esup> t"
inductive_cases Seq_tE[elim!]: "(c1;;c2,s1) \<Rightarrow>\<^bsup> p \<^esup>\<^esup> s3"
inductive_cases If_tE[elim!]: "(IF b \<noteq>0 THEN c1 ELSE c2,s) \<Rightarrow>\<^bsup> x  \<^esup>\<^esup>  t"
inductive_cases While_tE[elim]: "(WHILE b \<noteq>0 DO c,s) \<Rightarrow>\<^bsup> x  \<^esup>\<^esup>  t"
lemma Seq': "\<lbrakk> (c1,s1) \<Rightarrow>\<^bsup> x  \<^esup>\<^esup>  s2;  (c2,s2) \<Rightarrow>\<^bsup> y  \<^esup>\<^esup>  s3  \<rbrakk> \<Longrightarrow> (c1;;c2, s1) \<Rightarrow>\<^bsup> x + y  \<^esup>\<^esup>  s3"
  by auto

text "Rule inversion use examples:"
lemma "(IF b \<noteq>0 THEN SKIP ELSE SKIP, s) \<Rightarrow>\<^bsup> x  \<^esup>\<^esup>  t \<Longrightarrow> t = s"
  by blast

lemma assumes "(IF b \<noteq>0 THEN SKIP ELSE SKIP, s) \<Rightarrow>\<^bsup> x  \<^esup>\<^esup>  t"
  shows "t = s"
  using assms apply cases by auto
(*
lemma assign_t_simp:
  "((x ::= a,s) \<Rightarrow>\<^bsup>Suc (nlength (aval a s))\<^esup>\<^esup>   s') \<longleftrightarrow> (s' = s(x := aval a s))"
  by (auto)

subsection "Determinism of Big semantics of IMP-"
theorem big_step_t_determ2: "\<lbrakk> (c,s) \<Rightarrow>\<^bsup> p \<^esup>\<^esup> t; (c,s) \<Rightarrow>\<^bsup> q \<^esup>\<^esup> u \<rbrakk> \<Longrightarrow> (u = t \<and> p=q)"
  apply  (induction arbitrary: u q rule: big_step_Logt_induct)
    apply(elim Skip_tE) apply(simp)
    apply(elim Assign_tE) apply(simp)
  apply blast
    apply(elim If_tE) apply(simp) apply blast
    apply(elim If_tE)  apply (linarith) apply simp
    apply(erule While_tE) apply(simp) apply simp
  subgoal premises p for s1 b c x s2 y s3 z u q
    using p(7) apply(safe) 
      apply(erule While_tE)
        using p(1-6) apply fast
        using p(1-6) apply (simp)
      apply(erule While_tE)
        using p(1-6) apply fast
        using p(1-6) by (simp)
done

lemma bigstep_det: "(c1, s) \<Rightarrow>\<^bsup> p1\<^esup>\<^esup>t1 \<Longrightarrow> (c1, s) \<Rightarrow>\<^bsup> p \<^esup>\<^esup> t \<Longrightarrow> p1=p \<and> t1=t"
  using big_step_t_determ2 by simp


lemma seq_is_noop[simp]: "(SKIP, s) \<Rightarrow>\<^bsup>t\<^esup>\<^esup> s' \<longleftrightarrow> (t = Suc 0 \<and> s = s')" by auto

lemma seq_skip[simp]: "(c ;; SKIP, s) \<Rightarrow>\<^bsup>Suc t\<^esup>\<^esup> s' \<longleftrightarrow> (c, s) \<Rightarrow>\<^bsup>t\<^esup>\<^esup> s'" by auto

subsection "Progress property"
text "every command costs time"
lemma bigstep_progress: "(c, s) \<Rightarrow>\<^bsup> p \<^esup>\<^esup> t \<Longrightarrow> p > 0"
  apply(induct rule: big_step_Logt.induct, auto) done

lemma terminates_in_state_intro: "(c, s) \<Rightarrow>\<^bsup>t \<^esup>\<^esup> s' \<Longrightarrow> s' = s'' \<Longrightarrow> (c, s) \<Rightarrow>\<^bsup>t \<^esup>\<^esup> s''"
  by simp

lemma terminates_in_time_state_intro: "(c, s) \<Rightarrow>\<^bsup>t \<^esup>\<^esup> s' \<Longrightarrow> t = t' \<Longrightarrow> s' = s'' 
  \<Longrightarrow> (c, s) \<Rightarrow>\<^bsup>t' \<^esup>\<^esup> s''"
  by simp

lemma terminates_in_time_state_intro': "(c', s) \<Rightarrow>\<^bsup>t \<^esup>\<^esup> s' \<Longrightarrow> t = t' \<Longrightarrow> s' = s'' \<Longrightarrow> c' = c
  \<Longrightarrow> (c, s) \<Rightarrow>\<^bsup>t' \<^esup>\<^esup> s''"
  by simp

method dest_com  = 
  (match premises in a: "\<lbrakk>loop_cond; state_upd\<rbrakk> \<Longrightarrow> (_, s) \<Rightarrow>\<^bsup>t \<^esup>\<^esup> s'"
    for s s' t loop_cond state_upd \<Rightarrow> \<open>rule terminates_in_time_state_intro'[OF a]\<close>)

method dest_com' = 
  (match premises in a[thin]: "\<lbrakk>loop_cond; state_upd; (_, s) \<Rightarrow>\<^bsup>t \<^esup>\<^esup>s'\<rbrakk> \<Longrightarrow> P" 
    for s s' t loop_cond state_upd P  \<Rightarrow>
   \<open>match premises in b[thin]: "(While _ _, s2) \<Rightarrow>\<^bsup>t2 \<^esup>\<^esup>s2'"
      for s2 s2' t2 \<Rightarrow> \<open>insert a[OF _ _ b]\<close>\<close>)


method dest_com_init_while = 
  (match premises in a[thin]: "\<lbrakk>loop_cond; state_upd; ((_ ;; While _ _), s) \<Rightarrow>\<^bsup>t \<^esup>\<^esup> s'\<rbrakk> \<Longrightarrow> P" 
    for s s' t loop_cond state_upd P  \<Rightarrow>
   \<open>match premises in b[thin]: "((_ ;; While _ _), s2) \<Rightarrow>\<^bsup>t2 \<^esup>\<^esup> s2'"
      for s2 s2' t2 \<Rightarrow> \<open>insert a[OF _ _ b]\<close>\<close>)



lemma terminates_split_if : "(P s \<Longrightarrow> (c, s) \<Rightarrow>\<^bsup>t1 \<^esup>\<^esup> s1 ) \<Longrightarrow> 
(\<not> P s \<Longrightarrow> (c, s) \<Rightarrow>\<^bsup>t2 \<^esup>\<^esup>s2 ) \<Longrightarrow> (c,s) \<Rightarrow>\<^bsup>if P s then t1 else t2 \<^esup>\<^esup>  if P s then s1 else s2"
  by auto

lemma AssignD': 
"(x ::= a, s) \<Rightarrow>\<^bsup> 2\<^esup>\<^esup> s' \<Longrightarrow> s' = s (x:= aval a s)"
  by (auto simp add: eval_nat_numeral)

lemma com_only_vars: "\<lbrakk>(c, s) \<Rightarrow>\<^bsup> t  \<^esup>\<^esup> s'; x \<notin> set (Max_Constant.all_variables c)\<rbrakk> \<Longrightarrow> s x = s' x"
  by (induction arbitrary: t rule: big_step_Logt_induct)  auto

lemma Seq'': "\<lbrakk> (c1,s1) \<Rightarrow>\<^bsup> x  \<^esup>\<^esup> s2 \<and> P s2; P s2 \<Longrightarrow> (c2,s2) \<Rightarrow>\<^bsup> y  \<^esup>\<^esup> s3 \<and> Q s3; Q s3 \<Longrightarrow> R s3 \<rbrakk>
             \<Longrightarrow> (c1;;c2, s1) \<Rightarrow>\<^bsup> x + y  \<^esup>\<^esup> s3 \<and> R s3"
  by auto

lemma WhileI:
"\<lbrakk>(s1 b \<noteq> 0 \<Longrightarrow> (c,s1) \<Rightarrow>\<^bsup> x  \<^esup>\<^esup> s2 \<and> (WHILE b \<noteq>0 DO c, s2) \<Rightarrow>\<^bsup> y  \<^esup>\<^esup> s3);
  (s1 b = 0 \<Longrightarrow> s1 = s3);
  z = (if s1 b \<noteq> 0 then 1+x+y else 2)\<rbrakk>
        \<Longrightarrow> (WHILE b \<noteq>0 DO c, s1) \<Rightarrow>\<^bsup> z  \<^esup>\<^esup> s3" 
  by (auto simp add: WhileTrue WhileFalse numeral_2_eq_2)

lemma IfI:
"\<lbrakk>s b \<noteq> 0 \<Longrightarrow> (c1,s) \<Rightarrow>\<^bsup> x1  \<^esup>\<^esup> t1;
  s b = 0 \<Longrightarrow> (c2,s) \<Rightarrow>\<^bsup> x2  \<^esup>\<^esup> t2;
  y = (if s b \<noteq> 0 then x1 else x2) + 1;
  t = (if s b \<noteq> 0 then t1 else t2)\<rbrakk>
        \<Longrightarrow> (IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup> y  \<^esup>\<^esup> t" 
  by (auto simp add: IfTrue IfFalse)

lemma IfE: 
"(IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup> (if s b \<noteq> 0 then x1 else x2) + 1  \<^esup>\<^esup> (if s b \<noteq> 0 then s1 else s2) \<Longrightarrow> 
 \<lbrakk>\<lbrakk>s b \<noteq> 0; (if s b \<noteq> 0 then x1 else x2) + 1 = x1 + 1; 
  (if s b \<noteq> 0 then s1 else s2) = s1; (c1,s) \<Rightarrow>\<^bsup> x1  \<^esup>\<^esup> s1\<rbrakk> \<Longrightarrow> P;
  \<lbrakk>s b = 0; (if s b \<noteq> 0 then x1 else x2) + 1 = x2 + 1;
   (if s b \<noteq> 0 then s1 else s2) = s2; (c2,s) \<Rightarrow>\<^bsup> x2  \<^esup>\<^esup>s2\<rbrakk> \<Longrightarrow> P\<rbrakk>
        \<Longrightarrow> P"
  by (auto simp add: IfTrue IfFalse)

thm Seq_tE

lemma IfD:
"(IF b \<noteq>0 THEN c1 ELSE c2, s) \<Rightarrow>\<^bsup> (if s b \<noteq> 0 then x1 else x2) + 1  \<^esup>\<^esup> (if s b \<noteq> 0 then t1 else t2) \<Longrightarrow> 
 \<lbrakk>\<lbrakk>s b \<noteq> 0; (c1,s) \<Rightarrow>\<^bsup> x1  \<^esup>\<^esup> t1\<rbrakk> \<Longrightarrow> P;
  \<lbrakk>s b = 0; (c2,s) \<Rightarrow>\<^bsup> x2  \<^esup>\<^esup> t2\<rbrakk> \<Longrightarrow> P\<rbrakk>
        \<Longrightarrow> P" 
  by (auto simp add: IfTrue IfFalse)




lemma AssignI:
"\<lbrakk>s' = s (x:= aval a s)\<rbrakk>
        \<Longrightarrow> (x ::= a, s) \<Rightarrow>\<^bsup> Suc (nlength (aval a s))  \<^esup>\<^esup> s'" 
  by (auto simp add: Assign)


lemma AssignD: "(x ::= a, s) \<Rightarrow>\<^bsup> t  \<^esup>\<^esup> s' \<Longrightarrow> t = Suc (nlength (aval a s)) \<and> s' = s(x := aval a s)"
  by auto

lemma compose_programs_1:
  "(c2, s2) \<Rightarrow>\<^bsup> y  \<^esup>\<^esup>s3 \<Longrightarrow> (c1, s1) \<Rightarrow>\<^bsup> x \<^esup>\<^esup> s2 \<Longrightarrow> 
    ((c1;; c2, s1) \<Rightarrow>\<^bsup> x + y  \<^esup>\<^esup>s3 \<Longrightarrow> P)
   \<Longrightarrow> P"
  by auto

lemma compose_programs_2:
  "(c1, s1) \<Rightarrow>\<^bsup> x  \<^esup>\<^esup> s2 \<Longrightarrow> (c2, s2) \<Rightarrow>\<^bsup> y  \<^esup>\<^esup> s3 \<Longrightarrow> 
    ((c1;; c2, s1) \<Rightarrow>\<^bsup> x + y  \<^esup>\<^esup> s3 \<Longrightarrow> P)
   \<Longrightarrow> P"
  by auto

lemma While_tE_time:
"(WHILE b\<noteq>0 DO c, s) \<Rightarrow>\<^bsup> x  \<^esup>\<^esup> t \<Longrightarrow>
  (x = Suc (Suc 0) \<Longrightarrow> t = s \<Longrightarrow> s b = 0 \<Longrightarrow> P) \<Longrightarrow>
  (\<And>x' s2 y. 0 < s b \<Longrightarrow> (c, s) \<Rightarrow>\<^bsup> x'  \<^esup>\<^esup> s2 \<Longrightarrow> (WHILE b\<noteq>0 DO c, s2) \<Rightarrow>\<^bsup> y  \<^esup>\<^esup> t \<Longrightarrow> x = Suc (x' + y) \<Longrightarrow> P) \<Longrightarrow> P"
  by auto

lemma Seq_tE_While_init:
  "(WHILE v \<noteq>0 DO c2, s2) \<Rightarrow>\<^bsup> y  \<^esup>\<^esup> s3 \<Longrightarrow> (c1, s1) \<Rightarrow>\<^bsup> x  \<^esup>\<^esup> s2 \<Longrightarrow> 
    ((c1;; WHILE v \<noteq>0 DO c2, s1) \<Rightarrow>\<^bsup> x + y  \<^esup>\<^esup> s3 \<Longrightarrow> P)
   \<Longrightarrow> P"
  by auto


abbreviation TP0::"com\<Rightarrow>tape list" where
"TP0 prog\<equiv> IMPminus_state_to_TM_tape_list prog (\<lambda>x.(0::nat))"
*)

(*
An appropriate idd must satisfies the following condition:
(1) \forall x \in var_set prog, idd x \<ge>3 
\<and> Max(idd`(var_set prog))<last_tape 
*)

lemma length_tps_stable:
  assumes"transforms M tps1 t tps2"
  shows"length tps1=length tps2"
  sorry

lemma ineq4:" (a+b::nat)^4\<ge>a^4+b^4"
  sorry

lemma l0:
  fixes t::"nat"
  and t2::"nat"
  and prog::"com"
  and M::"machine"
  and idd::"vname\<Rightarrow>nat"
  and s::"AExp.state"
  and s'::"AExp.state"
  and tps'::"tape list"
  and v::"vname"
 assumes asm1:"M = while_TM_aux prog idd"
 and asm2:"(prog, s)\<Rightarrow>\<^bsup>t\<^esup>\<^esup>s'"                
 and asm3:"inj idd \<and> (\<forall>x\<in>(var_set prog). (idd x) \<ge>3) "
 and asm5:"transforms M tps t2 tps'"
shows"x-(idd) \<turnstile> tps' \<sim> s'"
  sorry

lemma l1:
  fixes t::"nat"
  and prog::"com"
  and M::"machine"
  and idd::"vname\<Rightarrow>nat"
  and s::"AExp.state"
  and s'::"AExp.state"
  and tps'::"tape list"
  and v::"vname"
 assumes asm1:"M = while_TM_aux prog idd"
 and asm2:"(prog, s)\<Rightarrow>\<^bsup>t\<^esup>\<^esup>s'"                
 and asm3:"inj idd \<and> (\<forall>x\<in>(var_set prog). (idd x) \<ge>3) "
 and asm5:"transforms M tps ((100::nat) * t ^ 4) tps'\<and>
       prog (idd) \<turnstile> tps' \<sim> s'"
shows" x-(idd) \<turnstile> tps' \<sim> s'"
sorry

(*
proof-
  have "(a + b :: nat)^4 = (\<Sum>k\<le>4. (of_nat (4 choose k)) * a^k * b^(4 - k))"  using binomial by blast
  have "...= a^4+((\<Sum>k\<le>3. (of_nat (4 choose k)) * a^k * b^(4 - k)))"  
    by (simp add: add.commute binomial_n_n numeral_1_eq_Suc_0 numeral_Bit0 numeral_Bit1 numeral_One of_nat_Suc of_nat_id sum.atMost_Suc)
  have "k\<le>3\<longrightarrow>a^k*b^(4-k)\<ge>0"by simp
  then have "(\<Sum>k\<le>3. (of_nat (4 choose k)) * a^k * b^(4 - k))\<ge>(\<Sum>k\<le>1. (of_nat (4 choose k)) * a^k * b^(4 - k))" by sledgehammer
*)
theorem lemma_IMPminus_to_TM_correct:
  fixes t::"nat"
  and prog::"com"
  and M::"machine"
  and idd::"vname\<Rightarrow>nat"
  and s::"AExp.state"
  and s'::"AExp.state"
  and tps::"tape list"
 assumes asm1:"M = while_TM_aux prog idd"
 and asm2:"(prog, s)\<Rightarrow>\<^bsup>t\<^esup>\<^esup>s'"                
 and asm3:"inj idd \<and> (\<forall>x\<in>(var_set prog). (idd x) \<ge>3) "
 and asm4:"prog (idd) \<turnstile> tps \<sim> s "
shows "\<exists>tps'. transforms M tps ((100::nat) * t ^ 4) tps'\<and>
       prog (idd) \<turnstile> tps' \<sim> s'"
  using assms(2,1,3-)
proof(induction arbitrary:s s' t M tps rule:big_step_Logt.induct)
  case (Skip s)
  then show ?case sorry
next
  case (Assign_vname x a s)
  then show ?case sorry
next
  case (Seq c1 s1 x s2 c2 y s3 z)
  then show ?case sorry
next
  case (IfTrue s b c1 x t y c2)
  then show ?case sorry
next
  case (IfFalse s b c2 x t y c1)
  then show ?case sorry
next
  case (WhileFalse s b c)
  then show ?case sorry
next
  case (WhileTrue s1 b c x s2 y s3 z)
  then show ?case sorry
qed




(*
  case SKIP
  have "s=s'\<and> t=1" using bigstep_det using SKIP.prems(2) by auto
  have "M = []"using SKIP.prems(1) while_TM_aux.simps(1) by blast
  then have "transforms M tps 0 tps" using transforms_Nil by auto
  then have "transforms M tps ((100::nat) * t ^ 4) tps" using transforms_monotone by blast
  moreover have " SKIP (idd) \<turnstile> tps \<sim> s" using SKIP.prems(4) by auto
  ultimately show ?case using \<open>s = s' \<and> t = 1\<close> by blast
next
  case (Assign v a)
  then have "M =((Aexp_TM idd a);;tm_cp_until 2 (idd v) {\<box>};;(tm_erase 2))" using while_TM_aux.simps(2) by presburger
  let ?M1="(Aexp_TM idd a)"
  let ?M2="tm_cp_until 2 (idd v) {\<box>};;(tm_erase 2)"
  let ?tps = "tps[2:= (\<lfloor>canrepr (aexpVal a s) \<rfloor>, 1)]"
  have "transforms ?M1 tps ?t ?tps" 
  show ?case proof (cases a)
    case (A x)
    then have "?M1= (atomExp_TM idd x 2)"by simp
    then show ?thesis proof (cases x)
      case (N x1)
      have l_1:" s'=s(v:= x1)" sorry
      have l0:"?M1=tm_set 2 (canrepr x1)"
        by (simp add: A N)
      have l1:"clean_tape (tps!2)" sorry
      have l2:"proper_symbols (canrepr 0)" by (simp add: proper_symbols_canrepr)
      have l3:"proper_symbols (canrepr x1)" by (simp add: proper_symbols_canrepr)
      have l4:"2<length tps" sorry
      have l5:"tps ::: 2 = \<lfloor>canrepr 0\<rfloor>" sorry
      let ?tps = "tps[2:= (\<lfloor>canrepr x1\<rfloor>, 1)]"
      let ?t="8 + tps :#: 2 + Suc (2 * length  (canrepr x1))" 
      have "transforms ?M1 tps ?t ?tps"using  transforms_tm_setI l1 l2 l3 l4 l5 
        by (metis Nat.add_0_right l0  mult_0_right nlength_0_simp)
       let ?tps = "tps[2:= (\<lfloor>canrepr x1\<rfloor>, 1)]"
      have "prog (idd) \<turnstile> ?tps \<sim> s'" sorry
      then show ?thesis sorry
    next
      case (V x2)
      then show ?thesis sorry
    qed
  next
    case (Plus x21 x22)
    then show ?thesis sorry
  next
    case (Sub x31 x32)
    then show ?thesis sorry
  next
    case (Parity x4)
    then show ?thesis sorry
  next
    case (RightShift x5)
    then show ?thesis sorry
  qed
next
  case (Seq prog1 prog2)
  obtain t1 t2 s'' where "(prog1, s)\<Rightarrow>\<^bsup>t1\<^esup>\<^esup>s''" and  "(prog2, s'')\<Rightarrow>\<^bsup>t-t1\<^esup>\<^esup>s'" and "t1\<le>t" using Seq.prems(2) by auto
  let ?M1 = "while_TM_aux prog1 idd"
  let ?M2 = "while_TM_aux prog2 idd"
  
  have "(prog1, s)\<Rightarrow>\<^bsup>t1\<^esup>\<^esup>s''" by (simp add: \<open>(prog1, s) \<Rightarrow>\<^bsup> t1 \<^esup>\<^esup> s''\<close>)
  have r1:"var_set prog1 \<subseteq>var_set (prog1;;prog2)" by fastforce
  have "(prog1;;prog2)  (idd) \<turnstile> tps \<sim> s" using Seq.prems(4) by blast
  then have "prog1 (idd) \<turnstile> tps \<sim> s " using r1 tape_list_equiv_IMPminus_state_for_Seq  by blast
  then obtain tps' where r1:" transforms ?M1 tps ((100::nat) * t1 ^ 4) tps'\<and>
     prog1 (idd) \<turnstile> tps' \<sim> s'' "  using Seq.IH(1) using Seq.prems(3) \<open>(prog1, s) \<Rightarrow>\<^bsup> t1 \<^esup>\<^esup> s''\<close> by fastforce
  have r2:"var_set prog2 \<subseteq>var_set (prog1;;prog2)" by fastforce
  have r3: "inj idd \<and> (\<forall>x\<in>(var_set prog2). (idd x) \<ge>3) " by (simp add: Seq.prems(3))
  have "\<forall>x\<in>(var_set prog2). x-(idd) \<turnstile> tps' \<sim> s''" using l1  r1 sorry
  then have " prog2 (idd) \<turnstile> tps' \<sim> s''" using tape_list_equiv_IMPminus_state_lem by blast
  then obtain tps'' where r2:" transforms ?M2 tps' ((100::nat) * (t-t1) ^ 4) tps''\<and>
     prog2 (idd) \<turnstile> tps'' \<sim> s' "using  \<open>(prog2, s'')\<Rightarrow>\<^bsup>t-t1\<^esup>\<^esup>s'\<close> using Seq.IH(2) r3 by presburger
  let ?M = "while_TM_aux (prog1;;prog2) idd"
  have "?M=?M1;;?M2" by auto
 
  have "length tps =length tps'\<and> length tps'=length tps''" using r1 r2  using length_tps_stable by blast
(*
lemma transforms_turing_machine_sequential:
  assumes "transforms M1 tps1 t1 tps2" and "transforms M2 tps2 t2 tps3"
  shows "transforms (M1 ;; M2) tps1 (t1 + t2) tps3"
*)
  then have r4:" transforms (?M1;;?M2) tps ((100::nat) * t1 ^ 4+(100::nat) * (t-t1)^ 4) tps''"
    using  transforms_turing_machine_sequential r1 r2 by blast
  have r5:"(100::nat) * t1 ^ 4+(100::nat) * (t-t1)^ 4\<le>(100::nat) * (t) ^ 4" using ineq4 \<open>t1 \<le> t\<close>    
  by (metis distrib_left_numeral le_add_diff_inverse mult_le_mono2)
  then have r6:" transforms (?M1;;?M2) tps ((100::nat) * t^ 4) tps''"
  using r4 transforms_monotone by blast
  have r7:"(prog1;;prog2)  (idd) \<turnstile> tps'' \<sim> s'" sorry
  show ?case using r7 r6 using Seq.prems(1) by auto
next
  case (If x1 prog1 prog2)
  then show ?case sorry
next
  case (While x1 prog)
  then show ?case sorry
qed
*)



end