theory WHILE_TM
  imports "IMP_Minus.AExp" "IMP_Minus.Com" "HOL-IMP.Star" Main  "IMP_Minus.Big_StepT"  "IMPminus_State_TM_Tape_List"
   Cook_Levin.Basics Cook_Levin.Combinations  Cook_Levin.Elementary   Cook_Levin.Arithmetic "TM_Minus" "big_step_Logt"
begin

\<comment> \<open>The following is a conceptualization of the direction from While (IMP-) to Turing Machine.

First, suppose that the number of variables involved in our While Program is less than or equal to n. 

We will prepare n+4 paper tapes for this purpose. The contents are as follows:

Tape zero is a read-only tape (this is the setting in the cook levin), and we will not use this tape at all here.

The first and second tapes are for operators, which are used for intermediate variables in the computation. 
For example, to perform z=x+y, we would first copy the value of x onto the first paper tape, and then the value of y 
onto the second paper tape. At the end of the final operation, the value of the second paper tape would become x + y. Finally, we would copy the value of the second paper tape to the paper tape corresponding to z. The third to n+2th paper tapes would be the second paper tape.

The third to n+2th tapes contain the values of the variables.

The last strip contains the rounding symbols, which will be used additionally in addition and subtraction operations. 
(The reason why this tape is placed last is also due to a setting in the cookie levin.)
\<close>



\<comment> \<open>This Turing machine is used to write the operand to the tp-th paper strip, 
so in use tp is generally equal to 1 or 2. when the operand is (N a), which is 
a constant, tm_set can be called directly, otherwise if it is (V v), we need to 
copy the value of the paper tape corresponding to v to the tp strip, and finally
 move the pointers of the two paper tapes to the first non-start character on the 
left.
idd is a function that corresponds the variable name to the corresponding paper tape 
number.
\<close>
  
fun atomExp_TM::"(vname\<Rightarrow>nat) \<Rightarrow>atomExp \<Rightarrow> nat \<Rightarrow>machine" where
"atomExp_TM idd (N a) tp =tm_set tp (canrepr a)"|
"atomExp_TM idd (V v) tp =tm_cp_until (idd v) tp {\<box>};;tm_cr (idd v);;tm_cr tp"


lemma rneigh_nat:"rneigh (\<lfloor>x\<rfloor>\<^sub>N,1)  {\<box>} (nlength x)" 
  unfolding rneigh_def apply auto using proper_symbols_canrepr by fastforce

lemma clean_implant:
  "clean_tape tp1\<longrightarrow>clean_tape tp2 \<longrightarrow>snd tp1=1\<longrightarrow>snd tp2=1\<longrightarrow>clean_tape (implant tp1 tp2  n)"
  unfolding clean_tape_def transplant_def by simp

lemma implant_cp:
  "implant  (\<lfloor>x\<rfloor>\<^sub>N,1) (\<lfloor>0\<rfloor>\<^sub>N,1) (nlength x) =(\<lfloor>x\<rfloor>\<^sub>N,1+(nlength x))" 
proof-
  have "(\<lambda>i. if Suc 0 \<le> i \<and> i < Suc (nlength x) then \<lfloor>x\<rfloor>\<^sub>N i 
         else fst (\<lfloor>0\<rfloor>\<^sub>N, Suc 0) i) =\<lfloor>x\<rfloor>\<^sub>N " 
  using bot_nat_0.not_eq_extremum contents_at_0 contents_outofbounds fst_conv less_eq_Suc_le nlength_0_simp not_less_eq by auto
  then have " (\<lambda>i. if Suc 0 \<le> i \<and> i < Suc (nlength x) then fst (\<lfloor>x\<rfloor>\<^sub>N, Suc 0)   i 
         else fst (\<lfloor>0\<rfloor>\<^sub>N, Suc 0) i) =
    \<lfloor>x\<rfloor>\<^sub>N " by (metis fst_conv)
 then have " (\<lambda>i. if Suc 0 \<le> i \<and> i < Suc (nlength x) then fst (\<lfloor>x\<rfloor>\<^sub>N, Suc 0) (Suc 0 + i - Suc 0)
         else fst (\<lfloor>0\<rfloor>\<^sub>N, Suc 0) i) = \<lfloor>x\<rfloor>\<^sub>N " using diff_add_inverse by presburger
  then have " (\<lambda>i. if Suc 0 \<le> i \<and> i < Suc (nlength x) then fst (\<lfloor>x\<rfloor>\<^sub>N, Suc 0) (snd (\<lfloor>x\<rfloor>\<^sub>N, Suc 0) + i - snd (\<lfloor>0\<rfloor>\<^sub>N, Suc 0))
         else fst (\<lfloor>0\<rfloor>\<^sub>N, Suc 0) i) =
    \<lfloor>x\<rfloor>\<^sub>N " by (metis snd_conv)
  then show ?thesis  
    by (simp add:implantI implantI' implantI'')
qed

\<comment> \<open>This following theorem proves that  atomExp_TM does accomplish our purpose, leaving 
the paper tapes intact except for the tp we want to modify.\<close>

theorem transforms_tm_atomI [transforms_intros]:
  fixes tp :: tapeidx
  and tps tps' :: "tape list"
  and a::"atomExp"
  and s::"AExp.state"
  and M::"machine"
  and idd::"vname \<Rightarrow>nat"
  assumes "M=atomExp_TM idd a tp" 
  and "tp<3" "tp > 0"
  and "proper_tape tps"
  and "(var_set_of_atomExp a) @ idd \<turnstile> tps \<sim> s "
  and "tps ! tp = (\<lfloor>0\<rfloor>\<^sub>N, 1)"
  and "ttt = 3 *(nlength (atomVal a s)) + 10"
  and "tps' = tps[tp := (\<lfloor>atomVal a s\<rfloor>\<^sub>N, 1)]"
  shows "transforms M tps ttt tps'"
  using assms
proof (cases a)
  have "proper_tape tps" using assms(4) by blast
  then have " length tps\<ge>4 \<and> (\<forall>i<(length tps). clean_tape (tps!i))" by simp
  then have "length tps \<ge>4" using assms(3) by simp
  then have ww:"tp<length tps" using assms(2) by auto
  case (N x1)
  have g0:"atomVal a s=x1" by (simp add: N)
  have g1:"M=tm_set tp (canrepr x1)" by (simp add: N assms(1))
  have g3:"clean_tape (tps!tp)" by (simp add: assms(6))
  have g10:"tps! tp =(\<lfloor>0\<rfloor>\<^sub>N,1)"  using assms(6) assms(7) by blast
  then have g4:"tps ::: tp =\<lfloor>0\<rfloor>\<^sub>N" by simp
  have g5:"proper_symbols (canrepr 0)" by simp
  have g6:"proper_symbols (canrepr x1)" by (simp add: proper_symbols_canrepr)
  let ?yt= "8 + tps :#: tp +  tp* length (canrepr 0) +  Suc (2 * length (canrepr x1))"
  have g8:"canrepr 0 =[]" by (simp add: canrepr_0)
  have g7:"length (canrepr 0) =0" by simp
  then have "?yt=8 + tps :#: tp +  Suc (2 * length (canrepr x1))" by auto
  then have "?yt=10 +2 * length (canrepr x1)" using g10 
  by (simp add: add.assoc add_Suc_shift eval_nat_numeral(3) numeral_Bit0 numeral_Bit1 snd_conv)
  let ?tps'= "tps[tp:=(\<lfloor>x1\<rfloor>\<^sub>N,1)]" 
  have "transforms M tps ?yt tps'"using ww g0 g1 g3 g4 g5 g6 transforms_tm_setI 
  by (metis assms(8) mult_0_right nlength_0_simp)
  have "?yt\<le>ttt"
  by (metis \<open>8 + tps :#: tp + tp * nlength 0 + Suc (2 * nlength x1) = 10 + 2 * nlength x1\<close> add.commute assms(7) g0 le_add2 mult_Suc nat_add_left_cancel_le numeral_2_eq_2 numeral_3_eq_3)
  then show ?thesis
  using \<open>transforms M tps (8 + tps :#: tp + tp * nlength 0 + Suc (2 * nlength x1)) tps'\<close> transforms_monotone by blast
next
  case (V vv)
  have g1:"M=tm_cp_until (idd vv) tp {\<box>};;tm_cr (idd vv);;tm_cr tp"  by (simp add: V assms(1))
  let ?M11="tm_cp_until (idd vv) tp {\<box>}"
  let ?M12="tm_cr (idd vv)"
  let ?M13="tm_cr tp"  
  let ?n1= "nlength (s vv)"
  have "var_set_of_atomExp a ={vv}" using V by auto
  then have y:"idd vv\<ge>3\<and> idd vv+1\<le>length tps" using assms(5) by auto
  then have "tp\<noteq>idd vv" using assms(2) by auto
  have g3:"tps!(idd vv) = (\<lfloor>s vv\<rfloor>\<^sub>N,1) "using assms(5) using \<open>var_set_of_atomExp a = {vv}\<close> by auto
  have g5:" rneigh (tps! (idd vv))  {\<box>} ?n1" using g3 rneigh_nat by auto
  let ?tps11="tps[(idd vv) := tps ! (idd vv) |+| ?n1, tp := implant (tps ! (idd vv)) (tps ! tp) ?n1]"
  let ?t1= "Suc ?n1"

  have "proper_tape tps" using assms(4) by blast
  then have " length tps\<ge>4 \<and> (\<forall>i<(length tps). clean_tape (tps!i))" by simp
  then have "length tps \<ge>4" using assms(3) by simp
  then have ww:"tp<length tps" using assms(2) by auto

  have "idd vv+1\<le>length tps" using y by auto
  then have g4:"transforms ?M11 tps ?t1 ?tps11" using transforms_tm_cp_untilI g3 g5  ww assms(4)
  by (metis Suc_eq_plus1  less_eq_Suc_le)

    have "clean_tape (tps!(idd vv))"
    by (simp add: clean_tape_ncontents g3)
    then have g10:"clean_tape (?tps11!(idd vv))"
    by (metis \<open>tp \<noteq> idd vv\<close> clean_tape_ncontents fst_conv g3 list_update_beyond not_le_imp_less nth_list_update_eq nth_list_update_neq')
    let ?t2= "?tps11:#:(idd vv) + 2"
    have f1:"?tps11!(idd vv) =tps!(idd vv) |+|?n1" 
   using \<open>idd vv + 1 \<le> length tps\<close> \<open>tp \<noteq> idd vv\<close> add.commute by auto
    have "vv-(idd) \<turnstile> tps \<sim> s" by (simp add: g3)
    have f2:"tps!(idd vv) =(\<lfloor>s vv\<rfloor>\<^sub>N, 1)" by (simp add: g3)
    then have f3:"fst (?tps11!(idd vv) )= \<lfloor>s vv\<rfloor>\<^sub>N" using f1 by auto
    have f4:"snd (?tps11!(idd vv) )= 1+?n1" using f1 g3 snd_conv by auto
    have t2:"?t2=?n1+3" using f4 by presburger
    let ?tps12 = "?tps11[(idd vv):=?tps11!(idd vv) |#=| 1]" 
    
    have "length tps =length ?tps11" by auto
    then have "idd vv <length ?tps11"  using \<open>idd vv + 1 \<le> length tps\<close> by linarith
    then have g11:"transforms ?M12 ?tps11 ?t2 ?tps12" using transforms_tm_crI g10 by blast

    have g12:"tp<length ?tps12" using length_list_update ww by fastforce
    have "clean_tape (tps ! tp)\<and>clean_tape (tps ! (idd vv))" using \<open>clean_tape (tps ! idd vv)\<close> assms(6) by auto
    then have g13:"clean_tape (?tps11 ! tp)" using  assms(6) clean_implant g3 length_list_update nth_list_update_eq snd_conv ww by auto
    let ?t3 ="?tps12:#:tp+ 2" 
    let ?tps13="?tps12[tp := ?tps12 !tp |#=| 1]"
    have "transforms ?M13 ?tps12 ?t3 ?tps13"using g13 transforms_tm_crI
      by (smt (verit) \<open>tp \<noteq> idd vv\<close> g12 nth_list_update_neq)
    then have g20:"transforms M tps (?t1+?t2+?t3) ?tps13" using g4 g11 transforms_turing_machine_sequential g1 by blast
    have qwq:"?tps12 =tps[ tp := implant (tps ! (idd vv)) (tps ! tp) ?n1]"
    by (metis (no_types, lifting) \<open>tp \<noteq> idd vv\<close> f3 g3 list_update_id list_update_overwrite list_update_swap)
    then have "?tps12:#:tp = ?n1+1" using assms(6) g3 implant_cp ww by force
    then have e:"?t3=?n1+3" by linarith
    have " fst (implant (tps ! (idd vv)) (tps ! tp) ?n1) =fst (tps!(idd vv))"
    using assms(6) g3 implant_cp by auto
  then have "?tps13=tps'" using V qwq by (simp add: assms(8) g3 list_update_overwrite ww)
    have u:"transforms M tps (?t1+?t2+?t3) tps'" 
    using \<open>tps[idd vv := tps ! idd vv |+| nlength (s vv), tp := implant (tps ! idd vv) (tps ! tp) (nlength (s vv)), idd vv := tps[idd vv := tps ! idd vv |+| nlength (s vv), tp := implant (tps ! idd vv) (tps ! tp) (nlength (s vv))] ! idd vv |#=| 1, tp := tps[idd vv := tps ! idd vv |+| nlength (s vv), tp := implant (tps ! idd vv) (tps ! tp) (nlength (s vv)), idd vv := tps[idd vv := tps ! idd vv |+| nlength (s vv), tp := implant (tps ! idd vv) (tps ! tp) (nlength (s vv))] ! idd vv |#=| 1] ! tp |#=| 1] = tps'\<close> g20 by blast
  have "?t1=?n1+1" by auto
  then have "?t1+?t2= 2*?n1+4" using e t2
    using f4 left_add_twice mult_2 by linarith
  then have "?t1+?t2+?t3=3*?n1+7"
  using \<open>tps[idd vv := tps ! idd vv |+| nlength (s vv), tp := implant (tps ! idd vv) (tps ! tp) (nlength (s vv)), idd vv := tps[idd vv := tps ! idd vv |+| nlength (s vv), tp := implant (tps ! idd vv) (tps ! tp) (nlength (s vv))] ! idd vv |#=| 1] :#: tp = nlength (s vv) + 1\<close> add_Suc_right add_mult_distrib eval_nat_numeral(3) by linarith
  then have "transforms M tps (3*?n1+7) tps'" 
    using u by presburger
  have "?n1=(nlength (atomVal a s))" by (simp add: V)
  have "(3 * nlength (s vv) + 7)\<le>(3 * nlength (s vv) + 10)" by simp
  then show ?thesis
  using \<open>transforms M tps (3 * nlength (s vv) + 7) tps'\<close> assms(8)
  by (metis \<open>nlength (s vv) = nlength (atomVal a s)\<close> assms(7) transforms_monotone)

qed

lemma aval_aexp_time:"nlength(aval a s) +1\<le> aexp_time a s"
  apply (cases a) unfolding aexp_time.simps aval.simps
      apply auto   using max_nlength nlength_sum apply presburger
    apply (simp add: add.commute le_SucI le_add2 nat_minus_add_max nlength_mono)
    using le_SucI mod_less_eq_dividend nlength_mono apply presburger
  by (simp add: le_Suc_eq nlength_mono)

\<comment> \<open>This following Turing machine runs an aexp expression through and presenting 
the final answer on the second paper tape.\<close>

fun Aexp_TM::"(vname\<Rightarrow>nat)\<Rightarrow>aexp \<Rightarrow> machine " where
"Aexp_TM idd (A a) = (atomExp_TM idd a 2)"|                                                    
"Aexp_TM idd (Plus a1 a2) = (atomExp_TM idd a1 1) ;;(atomExp_TM idd a2 2);; tm_add 1 2;;tm_erase_cr 1"|
"Aexp_TM idd (Sub a1 a2) = (atomExp_TM idd a1 1);;(atomExp_TM idd a2 2);;tm_cr 1;;tm_cr 2;;tm_minus 1 2"|
"Aexp_TM idd (Parity a) = (atomExp_TM idd a 1);;(tm_mod2 1 2);;tm_erase_cr 1"|
"Aexp_TM idd (RightShift a) =(atomExp_TM idd a 2);;(tm_div2 2)"


\<comment> \<open>The following function implementation processes the while program into a Turing machine.\<close>

fun While_TM::" com\<Rightarrow> (vname\<Rightarrow>nat) \<Rightarrow> machine" where
"While_TM   SKIP idd   = []"|
"While_TM  (Assign v a) idd  =(Aexp_TM idd a);;(tm_erase_cr (idd v));;tm_cp_until 2 (idd v)  {\<box>};;tm_cr (idd v);; (tm_erase_cr 2)"|
"While_TM  (Seq c1 c2) idd = ((While_TM c1 idd);;(While_TM c2 idd))"|
"While_TM  (If v c1 c2) idd =((tm_cmp 0 (idd v) 2);; IF (\<lambda>x. x!2=0) THEN (While_TM c1 idd) ELSE (While_TM c1 idd) ENDIF)"|
"While_TM  (While  v c) idd =(WHILE (tm_cmp 0 (idd v) 2) ; (\<lambda>x. x!2=0) DO While_TM c idd DONE)"

\<comment> \<open>Prove the correctness of this function above. It is worth noting that if we rely on my definition of time in
 the big_step_Logt file, we find that if a while program takes t steps to complete, then it turns out that the corresponding Turing machine is also capable of executing in linear time.\<close>
theorem transforms_tm_whileI [transforms_intros]:
  fixes t::"nat"
  and tps tps'::"tape list"
  and M::"machine"
  and idd::"vname\<Rightarrow>nat"    
  and s s'::"AExp.state"
  and S::"vname set"
  assumes asm1:"(prog, s)\<Rightarrow>\<^bsup>t\<^esup>\<^esup>s'"
  and asm2:"M = While_TM prog idd"     
  and asm3:"S @idd \<turnstile> tps \<sim> s "
  and asm4:"proper_tape tps"
  and asm5:"initial_tape tps"
  and asm6:"var_set prog \<subseteq> S" 
  shows "\<exists>tps'. transforms M tps (55 * t) tps'\<and>
       S @ idd \<turnstile> tps' \<sim> s'\<and> proper_tape tps'\<and> initial_tape tps'"
using assms
proof(induction "(prog, s)" t s' arbitrary: S s  idd  prog M tps rule:big_step_Logt.induct)
  case (Skip s)
  have "M = []" by (simp add: Skip.prems(1))
  then have x:"transforms M tps 0 tps\<and> S @ idd \<turnstile> tps \<sim> s\<and> proper_tape tps\<and> initial_tape tps" 
    using transforms_Nil Skip.prems(2) Skip.prems(3) Skip.prems(4) by auto
 then show ?case by (metis mult_is_0)
next
  case (Assign_vname v a s)
  let ?tps'="(tps[2:=  (\<lfloor>aval a s\<rfloor>\<^sub>N, 1)])"
  let ?M1="(Aexp_TM idd a)"
  have var_set_of_aexp_in_S:"var_set_of_aexp a \<subseteq> S" using Assign_vname.prems(5) by auto
  then have x:"(var_set_of_aexp a) @idd \<turnstile> tps \<sim> s" using Assign_vname.prems(2) using equiv_monoton by blast

  have tps_1:"tps!1=(\<lfloor>0\<rfloor>\<^sub>N, 1)"using Assign_vname.prems(4)  initial_tape.simps  by blast
  have tps_2:"tps!2=(\<lfloor>0\<rfloor>\<^sub>N, 1)"using Assign_vname.prems(4)  initial_tape.simps  by blast

  have tps_length :"length tps\<ge>4" using Assign_vname.prems(3) proper_tape.simps by blast
  have proper_tps :"proper_tape tps"using Assign_vname.prems(3) by auto
  have M1:"transforms ?M1 tps (37*(aexp_time a s)) ?tps'"  using assms x var_set_of_aexp_in_S tps_length tps_1 tps_2
  proof (cases a)
    case (A x)
    have 123:"0<(2::nat) \<and> (2::nat)<3" by simp
    let ?ttt="3*(nlength (atomVal x s))+10"
    have ttt_A_ineq:"?ttt\<le>37*(aexp_time a s)" using A aexp_time.simps(1) by presburger
    have M1_A:"?M1=(atomExp_TM idd x 2)" by (simp add: A)
    have x_A:"(var_set_of_atomExp x) @idd \<turnstile> tps \<sim> s" using Assign_vname.prems(2) A x by force
    have "aval a s=atomVal x s" using A by auto
    then have "?tps'=(tps[2:=  (\<lfloor>atomVal x s\<rfloor>\<^sub>N, 1)])" by simp
    then have f:"transforms ?M1 tps ?ttt ?tps'" using M1_A tps_2 transforms_tm_atomI var_set_of_aexp_in_S proper_tps 123 x_A
      by blast
    then show ?thesis using  ttt_A_ineq transforms_monotone by blast
  next
    case (Plus x1 x2)
    have M1_Plus:"?M1 = (atomExp_TM idd x1 1) ;;(atomExp_TM idd x2 2);; tm_add 1 2;;tm_erase_cr 1" by (simp add: Plus)
    let ?M11="(atomExp_TM idd x1 1)"
    let ?M12="(atomExp_TM idd x2 2)"
    let ?M13=" tm_add 1 2"
    let ?M14="tm_erase_cr 1"

    let ?tps1="(tps[1:=  (\<lfloor>atomVal x1 s\<rfloor>\<^sub>N, 1)])"
    let ?ttt1="3*(nlength (atomVal x1 s))+10"

    have "var_set_of_aexp a = \<Union> (var_set_of_atomExp ` atomExp_set_of_aexp a)" by simp
    then have "var_set_of_aexp a =var_set_of_atomExp x1 \<union> var_set_of_atomExp x2" by (simp add: Plus image_empty sup_bot.right_neutral)
    then have "var_set_of_atomExp x1 \<subseteq> S\<and>var_set_of_atomExp x2 \<subseteq> S" using var_set_of_aexp_in_S by simp
    then have  var_set_of_atomExp:" var_set_of_atomExp x1 @ idd  \<turnstile> tps \<sim> s \<and> var_set_of_atomExp x2 @ idd  \<turnstile> tps \<sim> s" by (meson Assign_vname.prems(2) equiv_monoton)
    then have "var_set_of_atomExp x1 @ idd  \<turnstile> tps \<sim> s" by blast
    then have M11:"transforms ?M11 tps ?ttt1 ?tps1" using tps_1 transforms_tm_atomI  using one_less_numeral_iff proper_tps semiring_norm(77) zero_less_one by blast

    let ?tps2="(?tps1[2:=  (\<lfloor>atomVal x2 s\<rfloor>\<^sub>N, 1)])"
   
    have "clean_tape (?tps1!1)" using tps_1 using clean_tape_ncontents tps_length by force
    then have proper_tps1:"proper_tape ?tps1" by (metis length_list_update nth_list_update_neq proper_tape.simps proper_tps)


    have tps1_2:"?tps1!2=(\<lfloor>0\<rfloor>\<^sub>N, 1)" by (simp add: tps_2)
    let ?ttt2="3 *(nlength (atomVal x2 s)) + 10"
    have "(\<forall>v\<in>S. idd v\<ge>3 \<and> idd v+1 < length tps\<and> v-idd \<turnstile> tps \<sim> s) \<and> inj_on idd S " using  var_set_of_atomExp
      using Assign_vname.prems(2) tape_list_equiv_IMPminus_state_on_a_set.simps by blast
    then have "(\<forall>v\<in>S. idd v\<ge>3 \<and> idd v+1 < length ?tps1\<and> v-idd \<turnstile> ?tps1 \<sim> s) \<and> inj_on idd S " 
    using numeral_le_one_iff semiring_norm(70) variable_tape_list_equiv_IMPminus_state.elims(2) variable_tape_list_equiv_IMPminus_state.elims(3) by auto
    then have "var_set_of_atomExp x2 @idd  \<turnstile> ?tps1 \<sim> s" using  var_set_of_atomExp 
    by (meson \<open>var_set_of_atomExp x1 \<subseteq> S \<and> var_set_of_atomExp x2 \<subseteq> S\<close> equiv_monoton tape_list_equiv_IMPminus_state_on_a_set.elims(3))
     then have M12:"transforms ?M12 ?tps1 ?ttt2 (?tps1[2:=(\<lfloor>atomVal x2 s\<rfloor>\<^sub>N, 1)])" using tps1_2  transforms_tm_atomI 
    by (metis less_add_one nat_1_add_1 numeral_Bit1 numerals(1) proper_tps1 zero_less_two)
    
  have tps2_length:"length tps =length ?tps2" by simp
  then have tps2_length_ineq:"length ?tps2\<ge>4" by (simp add: tps_length)
  then have tps2_1:"?tps2!1=(\<lfloor>atomVal x1 s\<rfloor>\<^sub>N, 1)" using less_one by auto
   then have tps2_2:"?tps2!2=(\<lfloor>atomVal x2 s\<rfloor>\<^sub>N, 1)" using tps2_length_ineq by force
  
   let ?ttt3="3 * max (nlength (atomVal x1 s)) (nlength (atomVal x2 s)) + 10"
    let ?tps3="?tps2[2:=(\<lfloor>atomVal x1 s + atomVal x2 s\<rfloor>\<^sub>N, 1)]"
    
    have M13:"transforms (?M13) ?tps2 ?ttt3 ?tps3" using  tps2_1 tps2_2 tps2_length_ineq transforms_tm_addI 
    by (smt (z3) add_eq_self_zero add_lessD1 add_less_mono le_eq_less_or_eq less_numeral_extra(1) less_numeral_extra(3) nat_1_add_1 numeral_Bit0 numeral_less_iff semiring_norm(76))

  have tps3_length:"length ?tps3= length tps" by simp
  then have tps3_length_ineq:"length ?tps3\<ge>4" by (simp add: tps_length)
  then have tps3_length_1:"1 < length ?tps3" by linarith 
  let ?tps4="?tps3[1 := (\<lfloor>[]\<rfloor>, 1)]"
  let ?ttt4="?tps3:#:1 + 2 * length (canrepr(atomVal x1 s)) + 6"
  
  have "?tps3:#:1 =1" using tps2_1 by auto
  then have ttt4:"?ttt4= 2 * nlength (atomVal x1 s) + 7" by presburger

  have tps4_tps':"?tps4 =?tps'"
  by (metis Plus Suc_eq_plus1 aval.simps(2) canrepr_0 list_update_id list_update_overwrite list_update_swap n_not_Suc_n one_add_one tps_1)


  have proper_symbols_x1:"proper_symbols (canrepr (atomVal x1 s)) " by (simp add: proper_symbols_canrepr)
  have tps3_1:"?tps3 ::: 1 = \<lfloor>canrepr (atomVal x1 s)\<rfloor> " using tps2_1 by auto
  then have M14:"transforms ?M14 ?tps3 ?ttt4 ?tps4" using transforms_tm_erase_crI proper_symbols_x1 tps3_length tps3_length_ineq
  proper_symbols_x1 tps3_1 tps3_length_1 by blast
  have "transforms ?M1 tps (?ttt1+?ttt2+?ttt3+?ttt4) ?tps4"using  transforms_turing_machine_sequential M11 M12 M13 M14
    by (smt (verit, ccfv_SIG) M1_Plus)
  then have M1:"transforms ?M1 tps ((?ttt1+?ttt2+?ttt3+?ttt4)) ?tps'" by (metis tps4_tps')

  have u1:"?ttt1\<le>3*(max (nlength (atomVal x1 s))  (nlength (atomVal x2 s))) +10" by simp
  moreover have u2:"?ttt2\<le>3*(max (nlength (atomVal x1 s))  (nlength (atomVal x2 s))) +10" by simp
  moreover  have u3:"?ttt3\<le>3*(max (nlength (atomVal x1 s))  (nlength (atomVal x2 s))) +10" by simp
  moreover  have u4:"?ttt4\<le>2*(max (nlength (atomVal x1 s))  (nlength (atomVal x2 s))) +7" 
    using max_nlength nlength_mono ordered_comm_semiring_class.comm_mult_left_mono semiring_norm(3) sup_ge1 sup_nat_def ttt4 zero_le_numeral by linarith
    
  moreover ultimately have u5:"?ttt1+?ttt2+?ttt3 +?ttt4\<le> 11* max (nlength (atomVal x1 s))  (nlength (atomVal x2 s))+37" by linarith

                         
    then have "?ttt1+?ttt2+?ttt3 +?ttt4\<le> 11* nlength  (max (atomVal x1 s) (atomVal x2 s)) +37"
      by (metis max_nlength nat_le_linear)
    then have "?ttt1+?ttt2+?ttt3 +?ttt4\<le> 37* nlength  (max (atomVal x1 s) (atomVal x2 s)) +37"
      by fastforce
    then moreover have "?ttt1+?ttt2+?ttt3 +?ttt4\<le>37* (aexp_time a s)"by (simp add: Plus)
    ultimately show ?thesis using M1 using transforms_monotone by blast
  next
    case (Sub x31 x32)
\<comment> \<open>For this part, you can refer to the definition in the file TM_Minus,
  but you need to imitate the theorems about the proof of add_TM.\<close>
    then show ?thesis sorry
  next
    case (Parity x)
    have p0:"?M1= (atomExp_TM idd x 1);;(tm_mod2 1 2);;tm_erase_cr 1"  using Aexp_TM.simps(4) Parity by blast
    let ?M11="(atomExp_TM idd x 1)"
    let ?M12="(tm_mod2 1 2)"
    let ?M13="tm_erase_cr 1"

    have "(var_set_of_atomExp x)\<subseteq> (var_set_of_aexp a)"  using Assign_vname.prems(5) x  by (simp add: Parity) 
    then have var_set_of_atomExp:"(var_set_of_atomExp x) @idd \<turnstile> tps \<sim> s" using equiv_monoton x by blast

    let ?ttt1="3 *(nlength (atomVal x s)) + 10"
    let ?tps1="(tps[1:=  (\<lfloor>atomVal x s\<rfloor>\<^sub>N, 1)])"
    have tps1_length:"length ?tps1= length tps" by simp
    then have tps1_length':" length ?tps1\<ge>4" by (simp add: tps_length)
    then have tps1_1:"?tps1 !1 =(\<lfloor>atomVal x s\<rfloor>\<^sub>N, 1)" by simp

    have M11:"transforms ?M11 tps ?ttt1 ?tps1" using var_set_of_atomExp transforms_tm_atomI
    using one_less_numeral_iff proper_tps semiring_norm(77) tps_1 zero_less_one by blast
    let ?tps2="(?tps1[2:= (\<lfloor>(atomVal x s) mod 2\<rfloor>\<^sub>N, 1)])"

    have tps1_2:"?tps1 !2 =(\<lfloor>0\<rfloor>\<^sub>N, 1)" by (simp add: tps_2)
    have length_tps:"length ?tps1=length tps" using Assign_vname.prems(3) by auto
    then have length_tps_ineq:"length tps \<ge>4" by (simp add: tps_length)
    then have "length ?tps1 \<ge>4" by simp
    then have M12:"transforms ?M12 ?tps1 1 ?tps2"  using tps1_1 tps1_2
    by (metis (no_types, lifting) add_lessD1 le_eq_less_or_eq less_add_same_cancel1 linordered_nonzero_semiring_class.zero_le_one nat_1_add_1 numeral_Bit0 transforms_tm_mod2I zero_less_two)
    
  let ?tps3="?tps2[1 := (\<lfloor>[]\<rfloor>, 1)]"
     let ?ttt3="?tps2:#: 1 + 2 * nlength (atomVal x s) + 6"
     have tps2_1:"?tps2!1=(\<lfloor>atomVal x s\<rfloor>\<^sub>N, 1)" using bits_mod_by_1 nth_list_update_neq one_mod_two_eq_one tps1_1 zero_neq_one by auto
     then  have "?tps2:#:1=1" by simp
     then have  ttt3:"?ttt3= 2 * nlength (atomVal x s) + 7"
       using \<open>tps[1 := (\<lfloor>atomVal x s\<rfloor>\<^sub>N, 1), 2 := (\<lfloor>atomVal x s mod 2\<rfloor>\<^sub>N, 1)] :#: 1 = 1\<close> by presburger
     have tps2_content_1:"?tps2 ::: 1 = \<lfloor>canrepr (atomVal x s)\<rfloor>"  using tps2_1 by fastforce
    have tps2_length:"length ?tps2=length tps" by simp
    then have tps2_length_1:"length ?tps2 >1" using tps_length by presburger
   
     have proper_symbols_x:"proper_symbols (canrepr (atomVal x s)) " by (simp add: proper_symbols_canrepr)
     then have M13:"transforms ?M13 ?tps2 ?ttt3 ?tps3" using  transforms_tm_erase_crI tps2_1 tps2_length_1  tps2_content_1 by blast
     have M1:"transforms ?M1 tps (?ttt1+1+?ttt3) ?tps3"using  transforms_turing_machine_sequential M11 M12 M13 
     by (smt (verit, ccfv_SIG) p0)
     then have "?ttt1+1+?ttt3 \<le> 5* (nlength (atomVal x s)) +18" using ttt3 by linarith
     then have u8:" ?ttt1+1+?ttt3 \<le> 37*(aexp_time a s)" by (simp add:Parity) 
      
     have "?tps3=?tps'" 
     by (metis Parity aval.simps(4) canrepr_0 list_update_id list_update_overwrite list_update_swap numeral_eq_one_iff semiring_norm(85) tps_1)
   then have "transforms ?M1 tps (?ttt1+1+?ttt3) ?tps'" 
     using M1  by presburger
    then show ?thesis using  transforms_monotone u8 by blast
  next
    case (RightShift x)
     let ?ttt="3*(nlength (atomVal x s))+10"
   
    have p0:"?M1=(atomExp_TM idd x 2);;(tm_div2 2)" by (simp add: RightShift)
    let ?M11="(atomExp_TM idd x 2)"
    let ?M12="(tm_div2 2)"
 
    have p1:"var_set_of_atomExp x @idd  \<turnstile> tps \<sim> s" using RightShift x by fastforce

   
    then have tps_2:"tps!2=(\<lfloor>0\<rfloor>\<^sub>N, 1)"  using tps_2 by blast
    let ?ttt1="3 *(nlength (atomVal x s)) + 10"
    
    let ?tps1="(tps[2:=  (\<lfloor>atomVal x s\<rfloor>\<^sub>N, 1)])"
    have M11:"transforms ?M11 tps ?ttt1 ?tps1" using p0 p1 tps_2  transforms_tm_atomI 
    using Assign_vname.prems(3) nat_1_add_1 nat_add_left_cancel_less numeral_Bit1 numerals(1) one_less_numeral_iff one_plus_numeral_commute semiring_norm(76) zero_less_two by force
    let ?tps2="(?tps1[2:=  (\<lfloor>(atomVal x s) div 2\<rfloor>\<^sub>N, 1)])"
    let ?ttt2= "2 * nlength (atomVal x s) + 3" 
    have tps1_2:"?tps1 !2 =(\<lfloor>atomVal x s\<rfloor>\<^sub>N, 1)" using tps_length by force
    have tps1_length:"length ?tps1=length tps" by simp
    then have tps1_length_ineq:"length ?tps1\<ge>4" by (simp add: tps_length)
    then have M12:"transforms ?M12 ?tps1 ?ttt2 ?tps2"
    by (metis (no_types, lifting) le_iff_add less_add_same_cancel2 numeral_Bit0 tps1_2 trans_less_add1 transforms_tm_div2I zero_less_numeral)
    then have M1:"transforms ?M1 tps (?ttt1+?ttt2) ?tps2" using M11 M12  transforms_turing_machine_sequential p0 by presburger

    have "?ttt1+?ttt2\<le>37*nlength (atomVal x s) + 37"  using Suc_leD eval_nat_numeral(3) linorder_linear mult_le_mono1 numeral_le_iff semiring_norm(69) semiring_norm(73) by auto
      then have u10:"?ttt1+?ttt2\<le>37*(Suc (aexp_time  a s))" 
      using RightShift by force 
    have "?tps2=?tps'" by (simp add: RightShift)
  then have "transforms ?M1 tps (?ttt1+?ttt2) ?tps'" using M1 by auto
  then show ?thesis using  u10
  using RightShift add.commute aexp_time.simps(5) mult_Suc_right transforms_monotone by auto
qed

  let ?M0="(tm_erase_cr (idd v))"
  let ?tps0="?tps'[idd v:=(\<lfloor>0\<rfloor>\<^sub>N, 1)]"

  have tps0:"?tps0=?tps'[idd v:=(\<lfloor>[]\<rfloor>,1)]" using ncontents_0 by auto
  let ?n0="nlength (s v)"
  let ?t0= "?tps' :#: (idd v) + 2 * (?n0) + 6"

  have v_in_S:"v\<in> S"
  using Assign_vname.prems(5) by auto
  
  have  tps1_length:"length ?tps0= length tps" by simp
  have  d:"(\<forall>v\<in>S. idd v\<ge>3 \<and> idd v+1 < length tps\<and> v-idd \<turnstile> tps \<sim> s) \<and> inj_on idd S "using Assign_vname.prems(2) by auto
  
  then have  tps1_length_ineq:"length ?tps'>idd v" using tps1_length v_in_S by auto
  have "v-idd \<turnstile> tps \<sim> s" using d v_in_S by blast
  then  have "((tps ! idd v) =(\<lfloor>s v\<rfloor>\<^sub>N, 1))" using tps1_length_ineq by simp
  then  have "tps :#: (idd v) =1 " using tps1_length_ineq by (simp add: sndI)
  then have "?tps'!(idd v) =(\<lfloor>s v\<rfloor>\<^sub>N, 1)" using  length_list_update nat_le_linear not_less_eq_eq plus_1_eq_Suc 
  using d semiring_norm(3) semiring_norm(5) v_in_S by fastforce
  then have "?tps' :#: (idd v) =1" by simp
  then have t0:"?t0=2*(?n0)+7" using add.commute add_mult_distrib nat_mult_1 one_plus_numeral semiring_norm(3)by linarith

  have "tps ::: (idd v) = \<lfloor>canrepr (s v)\<rfloor>" by (simp add: \<open>tps ! idd v = (\<lfloor>s v\<rfloor>\<^sub>N, 1)\<close>)
  then have tps1_iddv: "?tps' ::: (idd v) = \<lfloor>canrepr (s v)\<rfloor>"
  using \<open>tps[2 := (\<lfloor>aval a s\<rfloor>\<^sub>N, 1)] ! idd v = (\<lfloor>s v\<rfloor>\<^sub>N, 1)\<close> by fastforce
  have proper_symbol_sv:"proper_symbols (canrepr (s v))" using proper_symbols_canrepr by auto
  have tps4_length_ineq:"2<length ?tps0" using length_list_update nat_le_linear not_less_eq_eq plus_1_eq_Suc
  using tps_length by auto
  have M0:"transforms ?M0 ?tps' ?t0 ?tps0"using transforms_tm_erase_crI proper_symbol_sv tps1_length_ineq tps0 tps1_iddv
    by blast
  
  let ?M2="tm_cp_until 2 (idd v)  {\<box>}"
  let ?M3="tm_cr (idd v)"
  let ?M4=" (tm_erase_cr 2)"

  let ?n= "length (canrepr (aval a s))  "
 
  have tps0_rneigh:"rneigh (?tps0!2) {\<box>} ?n" using linorder_le_less_linear rneigh_nat tps_length
  by (metis \<open>tps ! idd v = (\<lfloor>s v\<rfloor>\<^sub>N, 1)\<close> \<open>tps[2 := (\<lfloor>aval a s\<rfloor>\<^sub>N, 1)] ! idd v = (\<lfloor>s v\<rfloor>\<^sub>N, 1)\<close> nth_list_update_eq nth_list_update_neq tps1_length tps1_length_ineq tps4_length_ineq tps_2)
  have tps0_length:"length tps=length ?tps0" by (simp add: Assign_vname.prems(2)) 
  then have  tps0_length_ineq:"length ?tps0\<ge>4" by (simp add: tps_length)
  
  let ?tps''="?tps0[2:=(?tps0!2)|+|?n, idd v:=implant (?tps0!2) (?tps0!(idd v)) ?n]"
  have tps2:"?tps''=?tps0[2:=(\<lfloor>aval a s\<rfloor>\<^sub>N, 1)|+|?n, idd v:=implant (\<lfloor>aval a s\<rfloor>\<^sub>N, 1) ((\<lfloor>[]\<rfloor>,1)) ?n]" 
  by (smt (z3) \<open>tps ! idd v = (\<lfloor>s v\<rfloor>\<^sub>N, 1)\<close> \<open>tps[2 := (\<lfloor>aval a s\<rfloor>\<^sub>N, 1)] ! idd v = (\<lfloor>s v\<rfloor>\<^sub>N, 1)\<close> canrepr_0 nth_list_update tps1_length tps1_length_ineq tps4_length_ineq tps_2)
  
  let ?M2="tm_cp_until 2 (idd v)  {\<box>}"
  have "v\<in>S" using Assign_vname.prems(5) by auto
  then have "idd v\<ge>3 \<and> idd v+1 < length tps\<and> v-idd \<turnstile> tps \<sim> s" using Assign_vname.prems(2) by auto
  then have "idd v+1 <length ?tps0" by force
  have M2:"transforms ?M2 ?tps0 (Suc ?n) ?tps''" using transforms_tm_cp_untilI  tps0_length_ineq
  by (metis length_list_update tps0_rneigh tps1_length_ineq tps4_length_ineq)
  let ?tps'''="?tps''[(idd v):=?tps'' ! (idd v) |#=| 1]"
  have "implant (\<lfloor>aval a s\<rfloor>\<^sub>N, 1) (\<lfloor>0\<rfloor>\<^sub>N ,1) ?n =
     (\<lambda>i. if snd  (\<lfloor>0\<rfloor>\<^sub>N ,1) \<le> i \<and> i < snd  (\<lfloor>0\<rfloor>\<^sub>N ,1) + ?n then  fst (\<lfloor>aval a s\<rfloor>\<^sub>N, 1) (snd (\<lfloor>aval a s\<rfloor>\<^sub>N, 1) + i - snd  (\<lfloor>0\<rfloor>\<^sub>N ,1)) else fst  (\<lfloor>0\<rfloor>\<^sub>N ,1) i,
      snd  (\<lfloor>0\<rfloor>\<^sub>N ,1) + ?n)" unfolding transplant_def 
  using implantI transplant_def by auto
  then have "implant (\<lfloor>aval a s\<rfloor>\<^sub>N, 1) (\<lfloor>0\<rfloor>\<^sub>N ,1) ?n =
     (\<lambda>i. if 1 \<le> i \<and> i < 1 + ?n then \<lfloor>aval a s\<rfloor>\<^sub>N  i else \<lfloor>0\<rfloor>\<^sub>N i,
      1 + ?n)" unfolding transplant_def  by (fastforce simp add:sndI fstI)
  then have "implant (\<lfloor>aval a s\<rfloor>\<^sub>N, 1) (\<lfloor>0\<rfloor>\<^sub>N ,1) ?n =
     (\<lfloor>aval a s\<rfloor>\<^sub>N,1 + ?n)" using implant_cp by blast
  have tps3:"?tps''=?tps'[2:=(\<lfloor>aval a s\<rfloor>\<^sub>N, 1)|+|?n, idd v:= (\<lfloor>aval a s\<rfloor>\<^sub>N,1 + ?n)]"
  by (smt (verit) \<open>implant (\<lfloor>aval a s\<rfloor>\<^sub>N, 1) (\<lfloor>0\<rfloor>\<^sub>N, 1) (nlength (aval a s)) = (\<lfloor>aval a s\<rfloor>\<^sub>N, 1 + nlength (aval a s))\<close> canrepr_0 list_update_overwrite list_update_swap tps2)
  
  let ?M3="tm_cr (idd v)"
  have tps''_length:"length ?tps'= length ?tps''" by simp
  then have tps''_length:"(idd v)<length ?tps''" using tps1_length_ineq by linarith
  have clean_tape_tps1:"\<forall>i<length ?tps'. clean_tape (?tps0!i)"
  by (metis clean_tape_ncontents length_list_update nth_list_update_eq nth_list_update_neq proper_tape.simps proper_tps)
  then have clean_tape_iddv:"clean_tape (?tps''!(idd v))" using  tps''_length using clean_tape_ncontents tps3 by auto
  let ?t2="?tps'' :#: (idd v) + 2" 
 
  have "?tps'':#:(idd v) =snd (?tps''!(idd v))" by blast
  then have "?tps'':#:(idd v) =snd (implant (?tps0!2) (?tps0!(idd v)) ?n)" using length_list_update nth_list_update_eq tps''_length by fastforce
  then have "?tps'':#:(idd v) =snd (transplant (?tps0!2) (?tps0!(idd v)) id ?n )" by blast
  then have "?tps'':#:(idd v) =snd (?tps0!(idd v))+?n" unfolding  transplant_def by simp
  then have "?tps'':#:(idd v) =1+?n"
  by (metis nth_list_update_eq snd_conv tps1_length_ineq)
  then have t2:"?t2 =?n+3" by linarith
  have M3:"transforms ?M3 ?tps'' ?t2 ?tps'''" using transforms_tm_crI  using clean_tape_iddv tps''_length by blast

  let ?M4="(tm_erase_cr 2)"
  let ?tps''''="?tps'''[2 := (\<lfloor>[]\<rfloor>, 1)]"
  let ?t3= "?tps''' :#: 2 + 2 * (?n) + 6"
  have "length ?tps'''>2" 
  using add_lessD1 length_list_update less_add_same_cancel1 nat_less_le numeral_Bit0 tps0_length tps_length zero_less_numeral by auto
  then have "?tps''' :#: 2 =1+?n"
proof -
  have f1: "2 < length tps" using tps_length by auto
   have f2: "\<not> (3::nat) \<le> 2"
    by auto
  have "\<forall>p n pa. tps[n := pa, 2 := p] ! 2 = p"
    using f1 by (simp add: length_list_update )
  then show ?thesis
    using f2 f1 \<open>3 \<le> idd v \<and> idd v + 1 < length tps \<and> v-idd \<turnstile> tps \<sim> s\<close> nth_list_update_neq  snd_conv by fastforce
qed
  then have t3:"?t3=3*(?n)+7"
  using add.commute add_mult_distrib nat_mult_1 one_plus_numeral semiring_norm(3) by linarith
  have tps3:"?tps''' ::: 2 = \<lfloor>canrepr (aval a s)\<rfloor>" 
  by (smt (z3) fst_conv length_list_update nth_list_update_eq nth_list_update_neq tps3 tps4_length_ineq)
  have proper_symbol_x:"proper_symbols (canrepr (aval a s))" using proper_symbols_canrepr by auto
  have tps4_length_ineq:"2<length ?tps''''" using length_list_update nat_le_linear not_less_eq_eq plus_1_eq_Suc tps0_length_ineq by auto
  have M4:"transforms ?M4 ?tps''' ?t3 ?tps''''"using transforms_tm_erase_crI proper_symbol_x tps4_length_ineq
  by (meson \<open>2 < length (tps[2 := (\<lfloor>aval a s\<rfloor>\<^sub>N, 1), idd v := (\<lfloor>0\<rfloor>\<^sub>N, 1), 2 := tps[2 := (\<lfloor>aval a s\<rfloor>\<^sub>N, 1), idd v := (\<lfloor>0\<rfloor>\<^sub>N, 1)] ! 2 |+| nlength (aval a s), idd v := implant (tps[2 := (\<lfloor>aval a s\<rfloor>\<^sub>N, 1), idd v := (\<lfloor>0\<rfloor>\<^sub>N, 1)] ! 2) (tps[2 := (\<lfloor>aval a s\<rfloor>\<^sub>N, 1), idd v := (\<lfloor>0\<rfloor>\<^sub>N, 1)] ! idd v) (nlength (aval a s)), idd v := tps[2 := (\<lfloor>aval a s\<rfloor>\<^sub>N, 1), idd v := (\<lfloor>0\<rfloor>\<^sub>N, 1), 2 := tps[2 := (\<lfloor>aval a s\<rfloor>\<^sub>N, 1), idd v := (\<lfloor>0\<rfloor>\<^sub>N, 1)] ! 2 |+| nlength (aval a s), idd v := implant (tps[2 := (\<lfloor>aval a s\<rfloor>\<^sub>N, 1), idd v := (\<lfloor>0\<rfloor>\<^sub>N, 1)] ! 2) (tps[2 := (\<lfloor>aval a s\<rfloor>\<^sub>N, 1), idd v := (\<lfloor>0\<rfloor>\<^sub>N, 1)] ! idd v) (nlength (aval a s))] ! idd v |#=| 1])\<close> tps3)
 
  let ?tt= "(37* (aexp_time a s)+?t0+(Suc ?n)+ ?t2+ ?t3)"
  have "M =?M1 ;;?M0;;?M2;;?M3;;?M4 " by (simp add: Assign_vname.prems(1))
  then moreover have M:"transforms M tps ?tt ?tps''''" using transforms_turing_machine_sequential M1 M0 M2 M3 M4 by meson

  have qwq:"11*(nlength(aval a s)+1) \<le>11*(aexp_time a s)" using  aval_aexp_time by (meson mult_le_mono2)
  have "48*(aexp_time a s)+(7*(nlength (s v)+1))\<le> 48*max (aexp_time a s) (nlength (s v)+1)+(7*(nlength (s v)+1))" by simp
  then  have "48*(aexp_time a s)+(7*(nlength (s v)+1))\<le> 48*max (aexp_time a s) (nlength (s v)+1)+(7*max (aexp_time a s) (nlength (s v)+1))"
  using max_def nat_mult_max_right by auto
  then have qwq2:"48*(aexp_time a s)+(7*(nlength (s v)+1))\<le> 55*max (aexp_time a s) (nlength (s v)+1)" 
  using mult.commute numeral_plus_numeral semiring_norm(3) by linarith

  have "?tt=(37* (aexp_time a s)+?t0+(Suc ?n)+?t2 +?t3)" by auto
  then have " ?tt=(37* (aexp_time a s)+(2*(nlength (s v))+7)+(Suc ?n)+?t2 +?t3)" using t0  by presburger
  then have " ?tt=(37* (aexp_time a s)+(2*(nlength (s v))+7)+(Suc ?n)+(?n+3) +3*(?n)+7)" using t2 t3  by presburger
  then have " ?tt=(37* (aexp_time a s)+(2*(nlength (s v))+7)+((Suc ?n)+((?n+3) +3*(?n)+7)))"  by presburger
  then have " ?tt =(37* (aexp_time a s)+(2*(nlength (s v))+7)+((Suc ?n)+(4*(?n)+10)))" by linarith
  then have " ?tt =(37* (aexp_time a s)+(2*(nlength (s v))+7)+(5*(?n)+11))" by linarith
  then have "?tt \<le>(37* (aexp_time a s)+(2*(nlength (s v))+7)+ 11*(?n+1))" by auto
  then have "?tt \<le>(37* (aexp_time a s)+(2*(nlength (s v))+7)+ 11*(nlength(aval a s)+1))" by simp
  then have"?tt \<le>(37* (aexp_time a s)+(2*(nlength (s v))+7)+11*(aexp_time a s))" using le_trans nat_add_left_cancel_le qwq by blast
  then have xx:"?tt \<le>(48* (aexp_time a s)+(2*(nlength (s v))+7))"  by linarith
  then have xx:"?tt \<le>(48* (aexp_time a s)+(7*(nlength (s v)+1)))" by simp
  then have "?tt \<le>48* (aexp_time a s)+(7*(nlength (s v)+1))" by simp
  then moreover have tt_ineq:"?tt\<le>55*(max (aexp_time a s) (nlength (s v)+1))" using qwq2 using le_trans by blast
  then have M':"transforms M tps (55*(max (aexp_time a s) (nlength (s v)+1))) ?tps''''" using M 
  using transforms_monotone by blast

  have "proper_tape ?tps0 " by (metis clean_tape_tps1 length_list_update proper_tape.elims(3) tps0_length_ineq)
  then  have proper_tape2:"proper_tape ?tps''"  
  by (smt (verit) \<open>implant (\<lfloor>aval a s\<rfloor>\<^sub>N, 1) (\<lfloor>0\<rfloor>\<^sub>N, 1) (nlength (aval a s)) = (\<lfloor>aval a s\<rfloor>\<^sub>N, 1 + nlength (aval a s))\<close> \<open>tps[2 := (\<lfloor>aval a s\<rfloor>\<^sub>N, 1), idd v := (\<lfloor>0\<rfloor>\<^sub>N, 1), 2 := tps[2 := (\<lfloor>aval a s\<rfloor>\<^sub>N, 1), idd v := (\<lfloor>0\<rfloor>\<^sub>N, 1)] ! 2 |+| nlength (aval a s), idd v := implant (tps[2 := (\<lfloor>aval a s\<rfloor>\<^sub>N, 1), idd v := (\<lfloor>0\<rfloor>\<^sub>N, 1)] ! 2) (tps[2 := (\<lfloor>aval a s\<rfloor>\<^sub>N, 1), idd v := (\<lfloor>0\<rfloor>\<^sub>N, 1)] ! idd v) (nlength (aval a s)), idd v := tps[2 := (\<lfloor>aval a s\<rfloor>\<^sub>N, 1), idd v := (\<lfloor>0\<rfloor>\<^sub>N, 1), 2 := tps[2 := (\<lfloor>aval a s\<rfloor>\<^sub>N, 1), idd v := (\<lfloor>0\<rfloor>\<^sub>N, 1)] ! 2 |+| nlength (aval a s), idd v := implant (tps[2 := (\<lfloor>aval a s\<rfloor>\<^sub>N, 1), idd v := (\<lfloor>0\<rfloor>\<^sub>N, 1)] ! 2) (tps[2 := (\<lfloor>aval a s\<rfloor>\<^sub>N, 1), idd v := (\<lfloor>0\<rfloor>\<^sub>N, 1)] ! idd v) (nlength (aval a s))] ! idd v |#=| 1] :#: 2 = 1 + nlength (aval a s)\<close> clean_tape_iddv length_list_update nth_list_update_eq nth_list_update_neq prod.collapse proper_tape.elims(1) tps1_length_ineq tps3)
  have  tps2_tps3:" ?tps'''= ?tps''[(idd v):=?tps'' ! (idd v) |#=| 1]" by fastforce
  then have "clean_tape (?tps''!(idd v))" using clean_tape_iddv by fastforce
  then have "clean_tape ( ?tps'' ! (idd v) |#=| 1) " unfolding clean_tape_def by force
  then have "clean_tape (?tps'''!(idd v))" using clean_tape_iddv tps2_tps3 
  by (metis nth_list_update_eq tps''_length)
  then have "proper_tape ?tps''' " using proper_tape2
  by (smt (verit) length_list_update nth_list_update_neq proper_tape.elims(1))
  then moreover have proper_tps4:"proper_tape ?tps''''"
  by (smt (verit) clean_tape_tps1 length_list_update nth_list_update_eq nth_list_update_neq proper_tape.elims(1) tps0 tps1_length_ineq)
 
  moreover have tps4_2:"( ?tps'''')!2 = (\<lfloor>0\<rfloor>\<^sub>N, 1)" 
  using \<open>2 < length (tps[2 := (\<lfloor>aval a s\<rfloor>\<^sub>N, 1), idd v := (\<lfloor>0\<rfloor>\<^sub>N, 1), 2 := tps[2 := (\<lfloor>aval a s\<rfloor>\<^sub>N, 1), idd v := (\<lfloor>0\<rfloor>\<^sub>N, 1)] ! 2 |+| nlength (aval a s), idd v := implant (tps[2 := (\<lfloor>aval a s\<rfloor>\<^sub>N, 1), idd v := (\<lfloor>0\<rfloor>\<^sub>N, 1)] ! 2) (tps[2 := (\<lfloor>aval a s\<rfloor>\<^sub>N, 1), idd v := (\<lfloor>0\<rfloor>\<^sub>N, 1)] ! idd v) (nlength (aval a s)), idd v := tps[2 := (\<lfloor>aval a s\<rfloor>\<^sub>N, 1), idd v := (\<lfloor>0\<rfloor>\<^sub>N, 1), 2 := tps[2 := (\<lfloor>aval a s\<rfloor>\<^sub>N, 1), idd v := (\<lfloor>0\<rfloor>\<^sub>N, 1)] ! 2 |+| nlength (aval a s), idd v := implant (tps[2 := (\<lfloor>aval a s\<rfloor>\<^sub>N, 1), idd v := (\<lfloor>0\<rfloor>\<^sub>N, 1)] ! 2) (tps[2 := (\<lfloor>aval a s\<rfloor>\<^sub>N, 1), idd v := (\<lfloor>0\<rfloor>\<^sub>N, 1)] ! idd v) (nlength (aval a s))] ! idd v |#=| 1])\<close> canrepr_0 nth_list_update_eq by fastforce
  have tps1_1:"( ?tps')!1 = (\<lfloor>0\<rfloor>\<^sub>N, 1)"  using tps_1 by auto
  then have tps2_1:"(?tps'')!1 = (\<lfloor>0\<rfloor>\<^sub>N, 1)" 
  using \<open>3 \<le> idd v \<and> idd v + 1 < length tps \<and> v-idd \<turnstile> tps \<sim> s\<close> nth_list_update_neq numeral_le_one_iff one_eq_numeral_iff semiring_norm(70) semiring_norm(85) by auto
  then have tps3_1:"(?tps''')!1 = (\<lfloor>0\<rfloor>\<^sub>N, 1)" 
  using \<open>3 \<le> idd v \<and> idd v + 1 < length tps \<and> v-idd \<turnstile> tps \<sim> s\<close> nlength_1_simp nlength_less_n nth_list_update_neq by auto
  then moreover  have tps4_1:"( ?tps'''')!1 = (\<lfloor>0\<rfloor>\<^sub>N, 1)" by simp

  have "(tps!0=(\<lfloor>0\<rfloor>\<^sub>N, 1)) \<and>  (tps!1=(\<lfloor>0\<rfloor>\<^sub>N, 1)) \<and> (tps!2=(\<lfloor>0\<rfloor>\<^sub>N, 1)) \<and> (tps!(length tps-1)= \<lceil>\<triangleright>\<rceil>)" using Assign_vname.prems(4) by simp
  then have tps_0:"(tps)!0= (\<lfloor>0\<rfloor>\<^sub>N, 1)"  by blast
  then have tps1_0:"( ?tps')!0= (\<lfloor>0\<rfloor>\<^sub>N, 1)"  by simp
  then have tps2_0:"(?tps'')!0 = (\<lfloor>0\<rfloor>\<^sub>N, 1)" 
  using \<open>3 \<le> idd v \<and> idd v + 1 < length tps \<and> v-idd \<turnstile> tps \<sim> s\<close> nth_list_update_neq numeral_le_one_iff one_eq_numeral_iff semiring_norm(70) semiring_norm(85) by auto
  then have tps3_0:"(?tps''')!0 = (\<lfloor>0\<rfloor>\<^sub>N, 1)" 
  using \<open>3 \<le> idd v \<and> idd v + 1 < length tps \<and> v-idd \<turnstile> tps \<sim> s\<close> nlength_1_simp nlength_less_n nth_list_update_neq by auto
  then  have tps4_0:"( ?tps'''')!0 = (\<lfloor>0\<rfloor>\<^sub>N, 1)" by simp

  have tps1_1:"( ?tps')!1= (\<lfloor>0\<rfloor>\<^sub>N, 1)"  using tps1_1 by auto
  then have tps2_1:"(?tps'')!1 = (\<lfloor>0\<rfloor>\<^sub>N, 1)" 
  using \<open>3 \<le> idd v \<and> idd v + 1 < length tps \<and> v-idd \<turnstile> tps \<sim> s\<close> nth_list_update_neq numeral_le_one_iff one_eq_numeral_iff semiring_norm(70) semiring_norm(85) by auto
  then have tps3_1:"(?tps''')!1 = (\<lfloor>0\<rfloor>\<^sub>N, 1)" 
  using \<open>3 \<le> idd v \<and> idd v + 1 < length tps \<and> v-idd \<turnstile> tps \<sim> s\<close> nlength_1_simp nlength_less_n nth_list_update_neq by auto
  then have tps4_1:"( ?tps'''')!1 = (\<lfloor>0\<rfloor>\<^sub>N, 1)" by simp

  have "(tps!(length tps-1)= \<lceil>\<triangleright>\<rceil>)"  using Assign_vname.prems(4) by simp
  then have tps1_last:"(?tps0!(length ?tps0-1))=\<lceil>\<triangleright>\<rceil>" 
  by (metis \<open>tps :#: idd v = 1\<close> nth_list_update_neq onesie_1 snd_conv tps1_length tps_2 zero_neq_one)
  then have tps1_last:"(?tps'!(length ?tps'-1))=\<lceil>\<triangleright>\<rceil>" 
  by (metis \<open>tps ! (length tps - 1) = \<lceil>1\<rceil>\<close> length_list_update nth_list_update_neq onesie_1 snd_conv tps_2 zero_neq_one)
  then have tps2_last:"(?tps''!(length ?tps''-1))=\<lceil>\<triangleright>\<rceil>" 
  using \<open>idd v + 1 < length (tps[2 := (\<lfloor>aval a s\<rfloor>\<^sub>N, 1), idd v := (\<lfloor>0\<rfloor>\<^sub>N, 1)])\<close> tps0_length_ineq by auto
 then have  tps3_last:"(?tps'''!(length ?tps'''-1))=\<lceil>\<triangleright>\<rceil>" 
  using \<open>idd v + 1 < length (tps[2 := (\<lfloor>aval a s\<rfloor>\<^sub>N, 1), idd v := (\<lfloor>0\<rfloor>\<^sub>N, 1)])\<close> by auto
  then  have tps4_last:"(?tps''''!(length ?tps''''-1)) = \<lceil>\<triangleright>\<rceil>"
  by (smt (z3) \<open>tps ! (length tps - 1) = \<lceil>1\<rceil>\<close> length_list_update nth_list_update_neq tps4_2 tps_2)
 
  
  then moreover  have initial_tps4:"initial_tape ?tps''''" using tps4_last tps4_1 tps4_2 tps4_0 using initial_tape.simps by blast

  have tps4_length:"length ?tps''''=length tps" by auto
  have aval_s:"aval a s= (s(v := aval a s)) v" by auto
  have tps4:"?tps''''=tps[(idd v):=(\<lfloor>aval a s\<rfloor>\<^sub>N, 1)]"
  by (smt (z3) \<open>implant (\<lfloor>aval a s\<rfloor>\<^sub>N, 1) (\<lfloor>0\<rfloor>\<^sub>N, 1) (nlength (aval a s)) = (\<lfloor>aval a s\<rfloor>\<^sub>N, 1 + nlength (aval a s))\<close> \<open>tps ! idd v = (\<lfloor>s v\<rfloor>\<^sub>N, 1)\<close> \<open>tps[2 := (\<lfloor>aval a s\<rfloor>\<^sub>N, 1)] ! idd v = (\<lfloor>s v\<rfloor>\<^sub>N, 1)\<close> canrepr_0 fst_conv length_list_update list_update_id list_update_overwrite list_update_swap nth_list_update_eq tps''_length tps4_length_ineq tps_2)
  then have tps4_sv:"?tps''''!(idd v) =(\<lfloor>(s(v := aval a s)) v\<rfloor>\<^sub>N, 1)" by (metis aval_s length_list_update nth_list_update_eq tps1_length_ineq)
  then have tps4_iddv:" v-idd \<turnstile> ?tps'''' \<sim> s(v := aval a s)" by (meson variable_tape_list_equiv_IMPminus_state.elims(3)) 
  then have i:"\<forall>i. (i\<noteq>idd v \<longrightarrow> ?tps''''!i=tps!i)" by (metis nth_list_update_neq tps4)

  have "\<forall>x\<in>S. x-idd \<turnstile> tps \<sim> s" using d by auto
  then have " \<forall>x\<in>S. ((tps ! idd x) =(\<lfloor>s x\<rfloor>\<^sub>N, 1))" by auto
  have inj_on_S:"inj_on  idd S" using d by blast
  then have " \<forall>x\<in>S. (idd x= idd v \<longrightarrow>x= v)" 
  by (meson inj_on_contraD v_in_S)
  then have " \<forall>x\<in>S. (x\<noteq>v\<longrightarrow>idd x\<noteq> idd v)"  by auto
  then have " \<forall>x\<in>S. (x\<noteq>v\<longrightarrow>?tps''''! (idd x)=tps!(idd x))" using i by  blast
   then have " \<forall>x\<in>S. (x\<noteq>v\<longrightarrow>?tps''''! (idd x)=(\<lfloor>s x\<rfloor>\<^sub>N, 1))"using tps4_sv by (metis \<open>\<forall>x\<in>S. tps ! idd x = (\<lfloor>s x\<rfloor>\<^sub>N, 1)\<close>)
   then have " \<forall>x\<in>S. (x\<noteq>v\<longrightarrow>?tps''''! (idd x)=(\<lfloor>(s(v := aval a s)) x\<rfloor>\<^sub>N, 1))" by simp
   then have " \<forall>x\<in>S. (x\<noteq>v\<longrightarrow>x-idd \<turnstile> ?tps'''' \<sim> s(v := aval a s))" by simp
   then have tps4_x:"\<forall>x\<in>S. x-idd \<turnstile> ?tps'''' \<sim> s(v := aval a s)"  using tps4_iddv by fastforce
   then have "(\<forall>x\<in>S. idd x\<ge>3 \<and> idd x+1 < length ?tps''''\<and> x-idd \<turnstile> ?tps'''' \<sim>  s(v := aval a s)) \<and> inj_on idd S " using d by (metis tps4_length tps4_x)
   then moreover have " S@idd \<turnstile> ?tps'''' \<sim> s(v := aval a s)"
   by (meson tape_list_equiv_IMPminus_state_on_a_set.elims(3))

  then have "transforms M tps (55*(max (aexp_time a s) (nlength (s v)+1))) ?tps''''\<and>
       S @ idd \<turnstile> ?tps'''' \<sim> s(v := aval a s)\<and> proper_tape ?tps''''\<and> initial_tape ?tps''''" using M' initial_tps4 proper_tps4 tt_ineq
    by blast
  then  show ?case
  by (metis Suc_eq_plus1)
next
  case (Seq c1 s0 t1 s1 c2 t2 s2 M)

  let ?M1 = "While_TM c1 idd"
  let ?M2 = "While_TM c2 idd"
  
  have r1:"var_set c1 \<subseteq>var_set (c1;;c2)" by fastforce 
  then have "var_set c1 \<subseteq>S" using Seq.prems(5) by auto
  have "S @ idd \<turnstile> tps \<sim> s0"using Seq.prems(2) by blast
  
  moreover have "proper_tape tps \<and>initial_tape tps"using Seq.prems(3) Seq.prems(4) by blast
  then obtain tps1 where r1:"transforms ?M1 tps (55 * t1) tps1 \<and>
     S @ idd \<turnstile> tps1 \<sim> s1\<and> proper_tape tps1 \<and> initial_tape tps1"
    using Seq.hyps(2) \<open>var_set c1 \<subseteq> S\<close> calculation by blast

  have r2:"var_set c2 \<subseteq> S" using Seq.prems(5) by auto
  then have "(\<forall> v\<in>S. idd v\<ge>3 \<and>idd v+1 < length tps\<and> v-idd \<turnstile> tps \<sim> s0) \<and>
     inj_on idd S" using Seq.prems(2) by force
  then have "(\<forall> v\<in>S. idd v\<ge>3 \<and>idd v+1 < length tps1 \<and> v-idd \<turnstile> tps1 \<sim> s1) \<and>
     inj_on idd S" by (metis r1 tape_list_equiv_IMPminus_state_on_a_set.elims(2))
  then have " S @ idd \<turnstile> tps1 \<sim> s1" using r1 by blast
  then obtain tps2 where r2:" transforms ?M2 tps1 (55 * t2 ) tps2 \<and>
     S @ idd \<turnstile> tps2 \<sim> s2 \<and> proper_tape tps2 \<and> initial_tape tps2" using Seq.hyps(4) r1 r2 by blast
  let ?M = "While_TM (c1;;c2) idd"

  have "S @ idd \<turnstile> tps2 \<sim> s2" using r2 by auto

  have w1:"transforms ?M1 tps (55 * t1) tps1" by (simp add: r1)
  have w2:"transforms ?M2 tps1 (55 * t2) tps2"  using r2 by auto

  then have q2:"transforms M tps (55*(t1+t2)) tps2" using w1 w2  transforms_turing_machine_sequential 
  by (simp add: Seq.prems(1))
  then show ?case using Seq.hyps(5) r2 by blast
next
  case (IfTrue s b c1 x t y c2)
(* 
For the next part of the proof, it is necessary to read the corresponding section in "Combination", 
    for example, transforms_tm_cmpI, transforms_loop_for ...
*)
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


end