theory WHILE_TM
  imports "IMP_Minus.AExp" "IMP_Minus.Com" "HOL-IMP.Star" Main  "IMP_Minus.Big_StepT"  "IMPminus_State_TM_Tape_List"
   Cook_Levin.Basics Cook_Levin.Combinations  Cook_Levin.Elementary   Cook_Levin.Arithmetic "TM_Minus" "big_step_Logt"
begin



fun aexpVal :: "aexp\<Rightarrow> AExp.state \<Rightarrow> val" where
"aexpVal (A a) s= (atomVal a s)"|
"aexpVal (Plus a1 a2) s= (atomVal a1 s)+(atomVal a2 s)"|
"aexpVal (Sub a1 a2) s= (atomVal a1 s)-(atomVal a2 s)"|
"aexpVal (Parity a) s = (atomVal a s) mod 2 "|
"aexpVal (RightShift a) s=(atomVal a s) div 2"

\<comment> \<open>This Turing machine is used to write the operand to the tpth paper strip, 
so in use tp is generally equal to 1 or 2. when the operand is N a, which is 
a constant, tm_set can be called directly, otherwise if it is V v, we need to 
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

\<comment> \<open>This following Turing machine runs an aexp expression through and presenting 
the final answer on the second paper tape.\<close>

fun Aexp_TM::"(vname\<Rightarrow>nat)\<Rightarrow>aexp \<Rightarrow> machine " where
"Aexp_TM idd (A a) = (atomExp_TM idd a 2)"|                                                    
"Aexp_TM idd (Plus a1 a2) = (atomExp_TM idd a1 1) ;;(atomExp_TM idd a2 2);; tm_add 1 2;;tm_erase_cr 1"|
"Aexp_TM idd (Sub a1 a2) = (atomExp_TM idd a1 1);;(atomExp_TM idd a2 2);;tm_cr 1;;tm_cr 2;;tm_minus 1 2"|
"Aexp_TM idd (Parity a) = (atomExp_TM idd a 1);;(tm_mod2 1 2);;tm_erase_cr 1"|
"Aexp_TM idd (RightShift a) =(atomExp_TM idd a 2);;(tm_div2 2)"

lemma o: "length l>n\<longrightarrow>l[n:=x]!n=x"
  by simp

\<comment> \<open>The following function implementation processes the while program into a Turing machine.\<close>

fun While_TM::" com\<Rightarrow> (vname\<Rightarrow>nat) \<Rightarrow> machine" where
"While_TM   SKIP idd   = []"|
"While_TM  (Assign v a) idd  = (Aexp_TM idd a);;tm_cp_until 2 (idd v)  {\<box>};;tm_cr (idd v);; (tm_erase_cr 2)"|
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
  shows "\<exists>tps'. transforms M tps (37 * t) tps'\<and>
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

(*
  have q1:"M= (Aexp_TM idd a);;tm_cp_until 2 (idd v) {\<box>};;tm_cr (idd v);; (tm_erase_cr 2)" by (simp add: Assign_vname.prems(1))
*) 

  let ?tps'="(tps[2:=  (\<lfloor>aexpVal a s\<rfloor>\<^sub>N, 1)])"
  let ?M1="(Aexp_TM idd a)"
  have var_set_of_aexp_in_S:"var_set_of_aexp a \<subseteq> S" using Assign_vname.prems(5) by auto
  then have x:"(var_set_of_aexp a) @idd \<turnstile> tps \<sim> s" using Assign_vname.prems(2) by auto

  have tps_1:"tps!1=(\<lfloor>0\<rfloor>\<^sub>N, 1)"using Assign_vname.prems(4)  initial_tape.simps  by blast
  have tps_2:"tps!2=(\<lfloor>0\<rfloor>\<^sub>N, 1)"using Assign_vname.prems(4)  initial_tape.simps  by blast

  have tps_length :"length tps\<ge>4" using Assign_vname.prems(3) proper_tape.simps by blast
  have proper_tps:"proper_tape tps"using Assign_vname.prems(3) by auto
  have M1:"transforms ?M1 tps (37*(aexp_time a s)) ?tps'"  using assms x var_set_of_aexp_in_S tps_length tps_1 tps_2
  proof (cases a)
    case (A x)
    have 123:"0<(2::nat) \<and> (2::nat)<3" by simp
    let ?ttt="3*(nlength (atomVal x s))+10"
    have ttt_A_ineq:"?ttt\<le>37*(aexp_time a s)" using A aexp_time.simps(1) by presburger
    have M1_A:"?M1=(atomExp_TM idd x 2)" by (simp add: A)
    have x_A:"(var_set_of_atomExp x) @idd \<turnstile> tps \<sim> s" using Assign_vname.prems(2) A x by force
    have "aexpVal a s=atomVal x s" using A by auto
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

    have "var_set_of_aexp a =var_set_of_atomExp x1\<union> var_set_of_atomExp x2" sorry
    have var_set_of_atomExp_x1:"var_set_of_atomExp x1 \<subseteq> S" using var_set_of_aexp_in_S sorry
    then have p1:" var_set_of_atomExp x1 @ idd  \<turnstile> tps \<sim> s" using Assign_vname.prems(2)  b2 by auto

    have "initial_tape tps"  using Assign_vname.prems(4) by auto
    then have "(tps!0=(\<lfloor>0\<rfloor>\<^sub>N, 1)) \<and>  (tps!1=(\<lfloor>0\<rfloor>\<^sub>N, 1)) \<and> (tps!2=(\<lfloor>0\<rfloor>\<^sub>N, 1)) \<and> (last tps= \<lceil>\<triangleright>\<rceil>)" by simp
    then have p2:"tps!1=(\<lfloor>0\<rfloor>\<^sub>N, 1)" by blast

    have e1:"transforms ?M11 tps ?ttt1 ?tps1" using p1 p2 transforms_tm_atomI 
    using Assign_vname.prems(3) by auto

    let ?tps2="(?tps1[2:=  (\<lfloor>atomVal x2 s\<rfloor>\<^sub>N, 1)])"
   
    have "var_set_of_atomExp x2\<subseteq> S"  using Plus b by auto
    then have p1':"var_set_of_atomExp x2 @idd  \<turnstile> tps \<sim> s" using Assign_vname.prems(2)  b2 by auto
    then have "\<forall>v \<in>(var_set_of_atomExp x2).  idd v\<ge>3 \<and>(idd v+1 < length tps)\<and> v-(idd) \<turnstile> tps \<sim> s" 
      using b2 by simp
    then have "\<forall>v \<in>(var_set_of_atomExp x2).  idd v\<ge>3 \<and>(idd v+1 < length ?tps1)\<and> v-(idd) \<turnstile> tps \<sim> s" 
      using b2 by simp
    then have "\<forall>v \<in>(var_set_of_atomExp x2). idd v\<ge>3\<and>((tps ! idd v) =(\<lfloor>s v\<rfloor>\<^sub>N, 1))" by simp
    then have "\<forall>v \<in>(var_set_of_atomExp x2). idd v\<ge>3\<and>((?tps1 ! idd v) =(\<lfloor>s v\<rfloor>\<^sub>N, 1))" by fastforce
    then have p1:"var_set_of_atomExp x2 @idd  \<turnstile> tps \<sim> s" using p1' by blast
     then have p1':"\<forall>v \<in>(var_set_of_atomExp x2).  idd v\<ge>3 \<and>(idd v+1 < length ?tps1)\<and> v-(idd) \<turnstile> ?tps1 \<sim> s"  by auto
       then have  p1'':"var_set_of_atomExp x2 @idd  \<turnstile> ?tps1 \<sim> s" by (simp add: b2)
  
    have "clean_tape (?tps1!1)"
      by (metis clean_tape_ncontents leI list_update_beyond nth_list_update_eq p2)
    have "proper_tape tps"  using Assign_vname.prems(3) by auto
    
    then have "length ?tps1\<ge>4 \<and> (\<forall>i<(length ?tps1). clean_tape (?tps1!i))" 
    by (metis (mono_tags, lifting) \<open>clean_tape (tps[1 := (\<lfloor>atomVal x1 s\<rfloor>\<^sub>N, 1)] ! 1)\<close> length_list_update nth_list_update_neq proper_tape.elims(2))
    then have p0':"proper_tape ?tps1" by auto
      
    have "initial_tape tps" using Assign_vname.prems(4) by auto
    then have "(tps!0=(\<lfloor>0\<rfloor>\<^sub>N, 1)) \<and>  (tps!1=(\<lfloor>0\<rfloor>\<^sub>N, 1)) \<and> (tps!2=(\<lfloor>0\<rfloor>\<^sub>N, 1)) \<and> (last tps= \<lceil>\<triangleright>\<rceil>)" by simp
    then have "tps!2=(\<lfloor>0\<rfloor>\<^sub>N, 1)" by blast
    then have p2':"?tps1!2=(\<lfloor>0\<rfloor>\<^sub>N, 1)" by auto
    let ?ttt2="3 *(nlength (atomVal x2 s)) + 10"

    have k1:"3>(2::nat)\<and> (0<(2::nat))" by simp
    then have e2:"transforms ?M12 ?tps1 ?ttt2 (?tps1[2:=(\<lfloor>atomVal x2 s\<rfloor>\<^sub>N, 1)])" using p0' p1' p2' transforms_tm_atomI 
    using p1'' by blast
    

    then have p6:"?tps2!1=(\<lfloor>atomVal x1 s\<rfloor>\<^sub>N, 1)"
     using \<open>4 \<le> length (tps[1 := (\<lfloor>atomVal x1 s\<rfloor>\<^sub>N, 1)]) \<and> (\<forall>i<length (tps[1 := (\<lfloor>atomVal x1 s\<rfloor>\<^sub>N, 1)]). clean_tape (tps[1 := (\<lfloor>atomVal x1 s\<rfloor>\<^sub>N, 1)] ! i))\<close> by auto
   then have p7:"?tps2!2=(\<lfloor>atomVal x2 s\<rfloor>\<^sub>N, 1)" 
    by (meson \<open>4 \<le> length (tps[1 := (\<lfloor>atomVal x1 s\<rfloor>\<^sub>N, 1)]) \<and> (\<forall>i<length (tps[1 := (\<lfloor>atomVal x1 s\<rfloor>\<^sub>N, 1)]). clean_tape (tps[1 := (\<lfloor>atomVal x1 s\<rfloor>\<^sub>N, 1)] ! i))\<close> le_trans nth_list_update_eq numeral_less_iff semiring_norm(76) semiring_norm(78) verit_comp_simplify1(3))
    let ?ttt3="3 * max (nlength (atomVal x1 s)) (nlength (atomVal x2 s)) + 10"

    let ?tps3="?tps2[2:=(\<lfloor>atomVal x1 s + atomVal x2 s\<rfloor>\<^sub>N, 1)]"
    have k2:"length ?tps2\<ge> 4"
    using \<open>4 \<le> length (tps[1 := (\<lfloor>atomVal x1 s\<rfloor>\<^sub>N, 1)]) \<and> (\<forall>i<length (tps[1 := (\<lfloor>atomVal x1 s\<rfloor>\<^sub>N, 1)]). clean_tape (tps[1 := (\<lfloor>atomVal x1 s\<rfloor>\<^sub>N, 1)] ! i))\<close> by auto
    
    
    then have e3:"transforms (?M13) ?tps2 ?ttt3 ?tps3" using k1 p6 p7  transforms_tm_addI 
    by (smt (verit) add_lessD1 le_eq_less_or_eq less_numeral_extra(4) mult_2 nat_1_add_1 nat_mult_less_cancel_disj numeral_Bit0 numeral_less_iff semiring_norm(76))
   let ?tps4="?tps3[1 := (\<lfloor>[]\<rfloor>, 1)]"
  let ?ttt4="?tps3:#: 1 + 2 * nlength (atomVal x1 s) + 6"
  have "?tps3:#: 1=1"using nat_1_add_1 p6 by fastforce
  then have u0:"?ttt4= 2 * nlength (atomVal x1 s) + 7" 
  using \<open>tps[1 := (\<lfloor>atomVal x1 s\<rfloor>\<^sub>N, 1), 2 := (\<lfloor>atomVal x2 s\<rfloor>\<^sub>N, 1), 2 := (\<lfloor>atomVal x1 s + atomVal x2 s\<rfloor>\<^sub>N, 1)] :#: 1 = 1\<close> by presburger

  have p7:"1<length ?tps3" 
  using \<open>4 \<le> length (tps[1 := (\<lfloor>atomVal x1 s\<rfloor>\<^sub>N, 1)]) \<and> (\<forall>i<length (tps[1 := (\<lfloor>atomVal x1 s\<rfloor>\<^sub>N, 1)]). clean_tape (tps[1 := (\<lfloor>atomVal x1 s\<rfloor>\<^sub>N, 1)] ! i))\<close> one_less_numeral_iff by auto
  have p8:"proper_symbols (canrepr (atomVal x1 s)) " by (simp add: proper_symbols_canrepr)
  then have e4:"transforms ?M14 ?tps3 ?ttt4 ?tps4" using  transforms_tm_erase_crI p7 p8 
  by (smt (verit) fst_conv less_2_cases_iff less_numeral_extra(4) nth_list_update_neq numeral_1_eq_Suc_0 numerals(1) p6)

  have e:"transforms ?M1 tps (?ttt1+?ttt2+?ttt3+?ttt4) ?tps4"using  transforms_turing_machine_sequential e1 e2 e3 e4
  by (smt (z3) \<open>Aexp_TM idd a = atomExp_TM idd x1 1 ;; atomExp_TM idd x2 2 ;; tm_add 1 2 ;; tm_erase_cr 1\<close>)

  have e2:"?tps4 =?tps'"
  by (metis Plus Suc_1 aexpVal.simps(2) list_update_id list_update_overwrite list_update_swap n_not_Suc_n ncontents_0 p2)
    have u1:"?ttt1\<le>3*(max (nlength (atomVal x1 s))  (nlength (atomVal x2 s))) +10" by simp
    have u2:"?ttt2\<le>3*(max (nlength (atomVal x1 s))  (nlength (atomVal x2 s))) +10" by simp
    have u3:"?ttt3\<le>3*(max (nlength (atomVal x1 s))  (nlength (atomVal x2 s))) +10" by simp
    have u4:"?ttt4\<le>2*(max (nlength (atomVal x1 s))  (nlength (atomVal x2 s))) +7" 
      using ordered_comm_semiring_class.comm_mult_left_mono u0 by linarith
    then have u5:"?ttt1+?ttt2+?ttt3 +?ttt4\<le> 11* (max (nlength (atomVal x1 s))  (nlength (atomVal x2 s))) +37" using u1 u2 u3 u4
      by linarith
    then have "...\<le> 11* nlength  (max (atomVal x1 s) (atomVal x2 s)) +37"
      by (metis max_nlength nat_le_linear)
    then have "...\<le> 37* nlength  (max (atomVal x1 s) (atomVal x2 s)) +37"
      by fastforce
    then have "...\<le>37* Suc( nlength (max (atomVal x1 s) (atomVal x2 s)))" 
    using mult_Suc_right by fastforce
  then have e3:"...\<le>37* (aexp_time a s)"by (simp add: Plus)
  then have "transforms ?M1 tps ((?ttt1+?ttt2+?ttt3+?ttt4)) ?tps'" using e e2 
  by metis
  then have "transforms ?M1 tps (37* (aexp_time a s)) ?tps'" 
  by (smt (verit, ccfv_threshold) Plus Suc_eq_plus1 \<open>11 * nlength (max (atomVal x1 s) (atomVal x2 s)) + 37 \<le> 37 * nlength (max (atomVal x1 s) (atomVal x2 s)) + 37\<close> aexp_time.simps(2) distrib_left_numeral max_nlength mult_numeral_1_right numerals(1) transforms_monotone u5)
    then show ?thesis by blast
  next
    case (Sub x31 x32)
    then show ?thesis sorry
  next
    case (Parity x)
    have p0:"?M1= (atomExp_TM idd x 1);;(tm_mod2 1 2);;tm_erase_cr 1"  using Aexp_TM.simps(4) Parity by blast
    let ?M11="(atomExp_TM idd x 1)"
    let ?M12="(tm_mod2 1 2)"
    let ?M13="tm_erase_cr 1"
    have p1:"(var_set_of_atomExp x)@idd\<turnstile> tps \<sim> s"using Parity b b2 by auto

    have "(tps!0=(\<lfloor>0\<rfloor>\<^sub>N, 1)) \<and>  (tps!1=(\<lfloor>0\<rfloor>\<^sub>N, 1)) \<and> (tps!2=(\<lfloor>0\<rfloor>\<^sub>N, 1)) \<and> (last tps= \<lceil>\<triangleright>\<rceil>)" using Assign_vname.prems(5)
    by (meson Assign_vname.prems(4) initial_tape.elims(2))
    then have p2:"tps!1=(\<lfloor>0\<rfloor>\<^sub>N, 1)" by blast
    let ?ttt1="3 *(nlength (atomVal x s)) + 10"
    let ?tps1="(tps[1:=  (\<lfloor>atomVal x s\<rfloor>\<^sub>N, 1)])"
    have tps1_length:"length ?tps1= length tps" by simp
    then have tps1_length':" length ?tps1\<ge>4" by (simp add: tps_length)
    then have p9:"?tps1 !1 =(\<lfloor>atomVal x s\<rfloor>\<^sub>N, 1)" by simp

    have e1:"transforms ?M11 tps ?ttt1 ?tps1" using p0 p2 transforms_tm_atomI 
    using Assign_vname.prems(4) one_less_numeral_iff p1 semiring_norm(77) zero_less_one 
    by (metis Assign_vname.prems(3))

    let ?tps2="(?tps1[2:= (\<lfloor>(atomVal x s) mod 2\<rfloor>\<^sub>N, 1)])"

    have p10:"?tps1 !2 =(\<lfloor>0\<rfloor>\<^sub>N, 1)" by (simp add: \<open>tps ! 0 = (\<lfloor>0\<rfloor>\<^sub>N, 1) \<and> tps ! 1 = (\<lfloor>0\<rfloor>\<^sub>N, 1) \<and> tps ! 2 = (\<lfloor>0\<rfloor>\<^sub>N, 1) \<and> last tps = \<lceil>1\<rceil>\<close>)
   
    have "length tps\<ge>4 \<and> (\<forall>i<(length tps). clean_tape (tps!i))" using Assign_vname.prems(3) by auto
    then have "length tps \<ge>4" by simp
    then have "length ?tps1 \<ge>4" by simp
    then have e2:"transforms ?M12 ?tps1 1 ?tps2" 
    by (smt (verit, ccfv_threshold) add_le_same_cancel1 le_neq_implies_less linorder_le_less_linear linordered_nonzero_semiring_class.zero_le_one numeral_Bit0 one_less_numeral_iff order_less_trans p10 p9 semiring_norm(76) transforms_tm_mod2I)
     let ?tps3="?tps2[1 := (\<lfloor>[]\<rfloor>, 1)]"
     let ?ttt3="?tps2:#: 1 + 2 * nlength (atomVal x s) + 6"
     have "?tps2!1=(\<lfloor>atomVal x s\<rfloor>\<^sub>N, 1)" using p9 by auto
     then  have "?tps2:#:1=1" by simp
     have u0:"?ttt3= 2 * nlength (atomVal x s) + 7" 
     using \<open>tps[1 := (\<lfloor>atomVal x s\<rfloor>\<^sub>N, 1), 2 := (\<lfloor>atomVal x s mod 2\<rfloor>\<^sub>N, 1)] :#: 1 = 1\<close> by presburger
     have p7:"1<length ?tps2"
     using \<open>4 \<le> length (tps[1 := (\<lfloor>atomVal x s\<rfloor>\<^sub>N, 1)])\<close> by auto
     have p8:"proper_symbols (canrepr (atomVal x s)) " by (simp add: proper_symbols_canrepr)
     then have e3:"transforms ?M13 ?tps2 ?ttt3 ?tps3" using  transforms_tm_erase_crI p7 p8 
     by (metis \<open>tps[1 := (\<lfloor>atomVal x s\<rfloor>\<^sub>N, 1), 2 := (\<lfloor>atomVal x s mod 2\<rfloor>\<^sub>N, 1)] ! 1 = (\<lfloor>atomVal x s\<rfloor>\<^sub>N, 1)\<close> fst_conv)
     have e:"transforms ?M1 tps (?ttt1+1+?ttt3) ?tps3"using  transforms_turing_machine_sequential e1 e2 e3 by (smt (verit, ccfv_SIG) p0)
     then have u5:"?ttt1+1+?ttt3 \<le> 5* (nlength (atomVal x s)) +18" using u0 by linarith
     then have u6:"?ttt1+1+?ttt3 \<le> 37*(nlength (atomVal x s))+37" by linarith
     then have u7:" ?ttt1+1+?ttt3 \<le> 37*(Suc (nlength (atomVal x s)))" by force
     then have u8:" ?ttt1+1+?ttt3 \<le> 37*(aexp_time a s)" by (simp add:Parity) 
      
     have "?tps3=?tps'"
     by (metis Parity aexpVal.simps(4) canrepr_0 list_update_id list_update_overwrite list_update_swap numeral_eq_one_iff p2 semiring_norm(85))
   then have "transforms ?M1 tps (?ttt1+1+?ttt3) ?tps'" 
     using e by presburger
    then show ?thesis using u8 transforms_monotone by blast
  next
    case (RightShift x)
     let ?ttt="3*(nlength (atomVal x s))+10"
   
    have p0:"?M1=(atomExp_TM idd x 2);;(tm_div2 2)" by (simp add: RightShift)
    let ?M11="(atomExp_TM idd x 2)"
    let ?M12="(tm_div2 2)"
 
    have "S @idd \<turnstile> tps \<sim> s " using Assign_vname.prems(2) by blast
    then have p1:"var_set_of_atomExp x @idd  \<turnstile> tps \<sim> s"
    using RightShift b b2 tape_list_equiv_IMPminus_state_on_a_set.elims(3) vars_of_aexp.simps(5) vars_of_aexp_set vars_of_atomExp_set by auto
    
    have "proper_tape tps" 
    using Assign_vname.prems(3) by auto
      
    have "initial_tape tps"
    using Assign_vname.prems(4) by auto
    then have "(tps!0=(\<lfloor>0\<rfloor>\<^sub>N, 1)) \<and>  (tps!1=(\<lfloor>0\<rfloor>\<^sub>N, 1)) \<and> (tps!2=(\<lfloor>0\<rfloor>\<^sub>N, 1)) \<and> (last tps= \<lceil>\<triangleright>\<rceil>)" by simp
    then have tps_2:"tps!2=(\<lfloor>0\<rfloor>\<^sub>N, 1)" by blast
    let ?ttt1="3 *(nlength (atomVal x s)) + 10"
    
    let ?tps1="(tps[2:=  (\<lfloor>atomVal x s\<rfloor>\<^sub>N, 1)])"
    have p8:"transforms ?M11 tps ?ttt1 ?tps1" using p0 p1 tps_2  transforms_tm_atomI 
    using Assign_vname.prems(3) nat_1_add_1 nat_add_left_cancel_less numeral_Bit1 numerals(1) one_less_numeral_iff one_plus_numeral_commute semiring_norm(76) zero_less_two by force
    let ?tps2="(?tps1[2:=  (\<lfloor>(atomVal x s) div 2\<rfloor>\<^sub>N, 1)])"
    let ?ttt2= "2 * nlength (atomVal x s) + 3" 
    have p9:"?tps1 !2 =(\<lfloor>atomVal x s\<rfloor>\<^sub>N, 1)" sorry
    have "length ?tps1\<ge>4" using Assign_vname.prems(2) asm6 sorry
    then have p10:"transforms ?M12 ?tps1 ?ttt2 ?tps2" 
    by (metis add_lessD1 le_eq_less_or_eq less_add_same_cancel1 nat_1_add_1 numeral_Bit0 p9 transforms_tm_div2I zero_less_two)
    then have e:"transforms ?M1 tps (?ttt1+?ttt2) ?tps2" using p8 p10  transforms_turing_machine_sequential p0 by presburger

    have "?ttt1+?ttt2\<le>37*nlength (atomVal x s) + 37"  using Suc_leD eval_nat_numeral(3) linorder_linear mult_le_mono1 numeral_le_iff semiring_norm(69) semiring_norm(73) by auto
      then have u10:"?ttt1+?ttt2\<le>37*(Suc (aexp_time  a s))" 
      using RightShift by force 
    have "?tps2=?tps'"
    by (simp add: RightShift)
  then have "transforms ?M1 tps (?ttt1+?ttt2) ?tps'" using e by auto
  then show ?thesis using  u10
  using RightShift add.commute aexp_time.simps(5) mult_Suc_right transforms_monotone by auto
qed
  let ?n= "length (canrepr (aexpVal a s))"
  have q3:"rneigh (?tps1!2) {\<box>} ?n" sorry
  have q4:"v\<in>var_set prog" using Assign_vname.hyps by auto
  then have q5:"k>2\<and>k>idd v" using Assign_vname.prems(3) by fastforce
  have q6:"k=length ?tps1" by (simp add: Assign_vname.prems(2))
  let ?tps2="?tps1[2:=(?tps1!2)|+|?n, idd v:=implant (?tps1!2) (?tps1!(idd v))?n]"
  let ?M2="tm_cp_until 2 (idd v)  {\<box>}"
  have q14:"transforms ?M2 ?tps1 (Suc ?n) ?tps2" using transforms_tm_cp_untilI q3 q6 q5  by blast

  let ?tps3="?tps2[(idd v):=?tps2 ! (idd v) |#=| 1]"
  let ?M3="tm_cr (idd v)"
  have q9:"k= length ?tps2" using q6 by auto
  then have q10:"(idd v)<length ?tps2" 
  using q5 by linarith
  have "\<forall>i<k. clean_tape (?tps1!i)"
  by (metis Assign_vname.prems(2) Assign_vname.prems(6) clean_tape_ncontents nth_list_update_eq nth_list_update_neq)
  then have q7:"\<forall>i<k. clean_tape (?tps2!i)" sorry
  have q11:"clean_tape (?tps2!(idd v))" using q5 q7 by blast
  let ?t2="?tps2 :#: (idd v) + 2" 
  have q15:"transforms ?M3 ?tps2 ?t2 ?tps3" using transforms_tm_crI q5 q7 q9 by blast
  let ?M4="(tm_erase_cr 2)"
  let ?tps4 ="?tps3[2 := (\<lfloor>[]\<rfloor>, 1)]"
  let ?t3= "?tps3 :#: 2 + 2 * (?n) + 6"
  have q13:"proper_symbols (canrepr (aexpVal a s))" 
    using proper_symbols_canrepr by auto
  have q12:"2<length ?tps4" using length_list_update q5 q9 by auto
  have q16:"transforms ?M4 ?tps3 ?t3 ?tps4"using transforms_tm_erase_crI q12 q13 
    by (simp add: fst_conv implant_self list_update_swap nth_list_update) 
  have "M =?M1 ;;?M2;;?M3;;?M4 " by (simp add: q1)
  let ?t= "((50::nat) * t ^ 4 +(Suc ?n)+ ?t2+ ?t3)"
  have q17:"transforms M tps ?t ?tps4" using q2 q14 q15 q16 transforms_turing_machine_sequential using q1 by blast
  have "?t< (50::nat) * t ^ 4" sorry
  then show ?case using q17 sorry
 
(*
    case (Parity x)
    have "prog = (v::=Parity x)" by (simp add: Parity f)
    have p0:"?M1= (atomExp_TM idd x 1);;(tm_mod2 1 2);;tm_erase_cr 1"  using Aexp_TM.simps(4) Parity by blast
    let ?M11="(atomExp_TM idd x 1)"
    let ?M12="(tm_mod2 1 2)"
    let ?M13="tm_erase_cr 1" 
(*
    have "var_set prog={v} \<union> var_set_of_aexp a" by (simp add: f)
    then have "var_set_of_atomExp x\<subseteq> var_set prog" sorry
    have "prog (idd) \<turnstile> tps \<sim> s " using Assign_vname.prems(4) by auto
    then have "Max (idd ` var_set prog)+1 < length tps \<and>
     (\<forall>v \<in> var_set prog. v-(idd) \<turnstile> tps \<sim> s)" by simp
    then have "\<forall>v \<in> var_set prog. v-(idd) \<turnstile> tps \<sim> s"  by blast
    then have p1:"\<forall>v \<in>(var_set_of_atomExp x). v-(idd) \<turnstile> tps \<sim> s" 
      using \<open>var_set_of_atomExp x \<subseteq> var_set prog\<close> by blast
    have "proper_tape tps" using Assign_vname.prems(6) by blast
*)
    have "var_set prog={v} \<union> var_set_of_aexp (Parity x)" using Parity b by fastforce
    then have "var_set_of_atomExp x\<subseteq> var_set prog" by force
    then have p1:"\<forall>v \<in>(var_set_of_atomExp x).  idd v\<ge>3 \<and>(idd v+1 < length tps)\<and> v-(idd) \<turnstile> tps \<sim> s"  using b2 by blast
   
    have "(tps!0=(\<lfloor>0\<rfloor>\<^sub>N, 1)) \<and>  (tps!1=(\<lfloor>0\<rfloor>\<^sub>N, 1)) \<and> (tps!2=(\<lfloor>0\<rfloor>\<^sub>N, 1)) \<and> (last tps= \<lceil>\<triangleright>\<rceil>)" using Assign_vname.prems(5) by auto
    then have p2:"tps!1=(\<lfloor>0\<rfloor>\<^sub>N, 1)" by blast
    let ?ttt1="3 *(nlength (atomVal x s)) + 10"
    let ?tps1="(tps[1:=  (\<lfloor>atomVal x s\<rfloor>\<^sub>N, 1)])"
    have e1:"transforms ?M11 tps ?ttt1 ?tps1" using p0 p2 transforms_tm_atomI 
    using Assign_vname.prems(4) one_less_numeral_iff p1 semiring_norm(77) zero_less_one by blast

    let ?tps2="(?tps1[2:= (\<lfloor>(atomVal x s) mod 2\<rfloor>\<^sub>N, 1)])"

    have "?tps1 =tps[1:=  (\<lfloor>atomVal x s\<rfloor>\<^sub>N, 1)]" by  blast
    then have p9:"?tps1 !1 =(\<lfloor>atomVal x s\<rfloor>\<^sub>N, 1)" sorry
    have p10:"?tps1 !2 =(\<lfloor>0\<rfloor>\<^sub>N, 1)" by (simp add: \<open>tps ! 0 = (\<lfloor>0\<rfloor>\<^sub>N, 1) \<and> tps ! 1 = (\<lfloor>0\<rfloor>\<^sub>N, 1) \<and> tps ! 2 = (\<lfloor>0\<rfloor>\<^sub>N, 1) \<and> last tps = \<lceil>1\<rceil>\<close>)
    have "2<length ?tps1" sorry
    then have e2:"transforms ?M12 ?tps1 1 ?tps2" 
    by (metis add_lessD1 linordered_nonzero_semiring_class.zero_le_one nat_1_add_1 p10 p9 transforms_tm_mod2I zero_less_two)

     let ?tps3="?tps2[1 := (\<lfloor>[]\<rfloor>, 1)]"
     let ?ttt3="?tps2:#: 1 + 2 * nlength (atomVal x s) + 6"
     have "?tps2!1=(\<lfloor>atomVal x s\<rfloor>\<^sub>N, 1)" using p9 by auto
     then  have "?tps2:#:1=1" by simp
     have u0:"?ttt3= 2 * nlength (atomVal x s) + 7" 
     using \<open>tps[1 := (\<lfloor>atomVal x s\<rfloor>\<^sub>N, 1), 2 := (\<lfloor>atomVal x s mod 2\<rfloor>\<^sub>N, 1)] :#: 1 = 1\<close> by presburger
     have p7:"1<length ?tps2" using Assign_vname.prems(2) asm6 by fastforce
     have p8:"proper_symbols (canrepr (atomVal x s)) " by (simp add: proper_symbols_canrepr)
     then have e3:"transforms ?M13 ?tps2 ?ttt3 ?tps3" using  transforms_tm_erase_crI p7 p8 
     by (metis \<open>tps[1 := (\<lfloor>atomVal x s\<rfloor>\<^sub>N, 1), 2 := (\<lfloor>atomVal x s mod 2\<rfloor>\<^sub>N, 1)] ! 1 = (\<lfloor>atomVal x s\<rfloor>\<^sub>N, 1)\<close> fst_conv)
     have e:"transforms ?M1 tps (?ttt1+1+?ttt3) ?tps3"using  transforms_turing_machine_sequential e1 e2 e3 by (smt (verit, ccfv_SIG) p0)
     then have u5:"?ttt1+1+?ttt3 \<le> 5* (nlength (atomVal x s)) +18" using u0 by linarith
    then show ?thesis sorry
  next
    case (RightShift x)
    let ?ttt="3*(nlength (atomVal x s))+10"
    have "prog = (v::=RightShift x)" by (simp add: RightShift f)
    have p0:"?M1=(atomExp_TM idd x 2);;(tm_div2 2)" by (simp add: RightShift)
    let ?M11="(atomExp_TM idd x 2)"
    let ?M12="(tm_div2 2)"
    have "var_set prog={v} \<union> var_set_of_aexp a" by (simp add: f)
    then have "var_set_of_atomExp x\<subseteq> var_set prog" sorry
    have "prog (idd) \<turnstile> tps \<sim> s " using Assign_vname.prems(4) by auto
    then have "Max (idd ` var_set prog)+1 < length tps \<and>
     (\<forall>v \<in> var_set prog. v-(idd) \<turnstile> tps \<sim> s)" by simp
    then have "\<forall>v \<in> var_set prog. v-(idd) \<turnstile> tps \<sim> s"  by blast
    then have p1:"\<forall>v \<in>(var_set_of_atomExp x). v-(idd) \<turnstile> tps \<sim> s" 
      using \<open>var_set_of_atomExp x \<subseteq> var_set prog\<close> by blast
    have "proper_tape tps" using Assign_vname.prems(6) by blast
      
    have "initial_tape tps" using Assign_vname.prems(7) by blast
    then have "(tps!0=(\<lfloor>0\<rfloor>\<^sub>N, 1)) \<and>  (tps!1=(\<lfloor>0\<rfloor>\<^sub>N, 1)) \<and> (tps!2=(\<lfloor>0\<rfloor>\<^sub>N, 1)) \<and> (last tps= \<lceil>\<triangleright>\<rceil>)" by simp
    then have p2:"tps!2=(\<lfloor>0\<rfloor>\<^sub>N, 1)" by blast
    let ?ttt1="3 *(nlength (atomVal x s)) + 10"
    have p3:"Max (idd ` var_set_of_atomExp x)+1<length tps" sorry
    have p4:"Min (idd ` var_set_of_atomExp x)\<ge>3" sorry

    let ?tps1="(tps[2:=  (\<lfloor>atomVal x s\<rfloor>\<^sub>N, 1)])"
    have p8:"transforms ?M11 tps ?ttt1 ?tps1" using p0 p1 p2 p3 p4 transforms_tm_atomI by (metis Assign_vname.prems(6) le_refl nat_1_add_1 nlength_3 nlength_less_n zero_less_two)  

    let ?tps2="(?tps1[2:=  (\<lfloor>(atomVal x s) div 2\<rfloor>\<^sub>N, 1)])"
    let ?ttt2= "2 * nlength (atomVal x s) + 3" 
    have p9:"?tps1 !2 =(\<lfloor>atomVal x s\<rfloor>\<^sub>N, 1)" using Assign_vname.prems(2) asm6 by auto
    have "2<length ?tps1" using Assign_vname.prems(2) asm6 by auto
    then have p10:"transforms ?M12 ?tps1 ?ttt2 ?tps2" using transforms_tm_div2I p9 by (metis zero_less_numeral)

    then have "transforms ?M1 tps (?ttt1+?ttt2) ?tps2" using p8 p10  transforms_turing_machine_sequential p0 by presburger
    then show ?thesis sorry
  qed
  let ?n= "length (canrepr (aexpVal a s))"
  have q3:"rneigh (?tps1!2) {\<box>} ?n" sorry
  have q4:"v\<in>var_set prog" using Assign_vname.hyps by auto
  then have q5:"k>2\<and>k>idd v" using Assign_vname.prems(3) by fastforce
  have q6:"k=length ?tps1" by (simp add: Assign_vname.prems(2))
  let ?tps2="?tps1[2:=(?tps1!2)|+|?n, idd v:=implant (?tps1!2) (?tps1!(idd v))?n]"
  let ?M2="tm_cp_until 2 (idd v)  {\<box>}"
  have q14:"transforms ?M2 ?tps1 (Suc ?n) ?tps2" using transforms_tm_cp_untilI q3 q6 q5  by blast

  let ?tps3="?tps2[(idd v):=?tps2 ! (idd v) |#=| 1]"
  let ?M3="tm_cr (idd v)"
  have q9:"k= length ?tps2" using q6 by auto
  then have q10:"(idd v)<length ?tps2" 
  using q5 by linarith
  have "\<forall>i<k. clean_tape (?tps1!i)"
  by (metis Assign_vname.prems(2) Assign_vname.prems(6) clean_tape_ncontents nth_list_update_eq nth_list_update_neq)
  then have q7:"\<forall>i<k. clean_tape (?tps2!i)" sorry
  have q11:"clean_tape (?tps2!(idd v))" using q5 q7 by blast
  let ?t2="?tps2 :#: (idd v) + 2" 
  have q15:"transforms ?M3 ?tps2 ?t2 ?tps3" using transforms_tm_crI q5 q7 q9 by blast
  let ?M4="(tm_erase_cr 2)"
  let ?tps4 ="?tps3[2 := (\<lfloor>[]\<rfloor>, 1)]"
  let ?t3= "?tps3 :#: 2 + 2 * (?n) + 6"
  have q13:"proper_symbols (canrepr (aexpVal a s))" 
    using proper_symbols_canrepr by auto
  have q12:"2<length ?tps4" using length_list_update q5 q9 by auto
  have q16:"transforms ?M4 ?tps3 ?t3 ?tps4"using transforms_tm_erase_crI q12 q13 
    by (simp add: fst_conv implant_self list_update_swap nth_list_update) 
  have "M =?M1 ;;?M2;;?M3;;?M4 " by (simp add: q1)
  let ?t= "((50::nat) * t ^ 4 +(Suc ?n)+ ?t2+ ?t3)"
  have q17:"transforms M tps ?t ?tps4" using q2 q14 q15 q16 transforms_turing_machine_sequential using q1 by blast
  have "?t< (50::nat) * t ^ 4" sorry
  then show ?case using q17 sorry
next
*)

 show ?case sorry
next
  case (Seq c1 s0 t1 s1 c2 t2 s2 M)
(*
 assumes asm1:"(prog, s)\<Rightarrow>\<^bsup>t\<^esup>\<^esup>s'"
 and asm2:"M = While_TM prog idd"     
 and asm3:"prog (idd) \<turnstile> tps \<sim> s "
 and asm4:"proper_tape tps"
 and asm5:"initial_tape tps"
*)

  let ?M1 = "While_TM c1 idd"
  let ?M2 = "While_TM c2 idd"
  
  have r1:"var_set c1 \<subseteq>var_set (c1;;c2)" by fastforce 
  then have "var_set c1 \<subseteq>S" using Seq.prems(5) by auto
  have "S @ idd \<turnstile> tps \<sim> s0"using Seq.prems(2) by blast
  
  moreover have "proper_tape tps \<and>initial_tape tps"using Seq.prems(3) Seq.prems(4) by blast
  then obtain tps1 where r1:"transforms ?M1 tps (37 * t1) tps1 \<and>
     S @ idd \<turnstile> tps1 \<sim> s1\<and> proper_tape tps1 \<and> initial_tape tps1"
    using Seq.hyps(2) \<open>var_set c1 \<subseteq> S\<close> calculation by blast

  have r2:"var_set c2 \<subseteq> S" using Seq.prems(5) by auto
  then have "(\<forall> v\<in>S. idd v\<ge>3 \<and>idd v+1 < length tps\<and> v-idd \<turnstile> tps \<sim> s0) \<and>
     inj idd" using Seq.prems(2) by force
  then have "(\<forall> v\<in>S. idd v\<ge>3 \<and>idd v+1 < length tps1 \<and> v-idd \<turnstile> tps1 \<sim> s1) \<and>
     inj idd" by (metis r1 tape_list_equiv_IMPminus_state_on_a_set.elims(2))
  then have " S @ idd \<turnstile> tps1 \<sim> s1" using r1 by blast
  then obtain tps2 where r2:" transforms ?M2 tps1 (37 * t2 ) tps2 \<and>
     S @ idd \<turnstile> tps2 \<sim> s2 \<and> proper_tape tps2 \<and> initial_tape tps2" using Seq.hyps(4) r1 r2 by blast
  let ?M = "While_TM (c1;;c2) idd"

  have "S @ idd \<turnstile> tps2 \<sim> s2" using r2 by auto

  have w1:"transforms ?M1 tps (37 * t1) tps1" by (simp add: r1)
  have w2:"transforms ?M2 tps1 (37 * t2) tps2"  using r2 by auto

  then have q2:"transforms M tps (37*(t1+t2)) tps2" using w1 w2  transforms_turing_machine_sequential 
  by (simp add: Seq.prems(1))

(*
  have "transforms M tps (37*(t1+t2)) tps2 \<and>
     (c1;;c2) (idd) \<turnstile> tps2 \<sim> s2 \<and>proper_tape tps2 \<and> initial_tape tps2"  using q1 q2 r2 by blast 

  have "(c1;;c2, s0)\<Rightarrow>\<^bsup>t1+t2\<^esup>\<^esup>s2" 
  using Seq.hyps(1) Seq.hyps(3) by auto
*)

  then show ?case using Seq.hyps(5) r2 by blast
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
then show ?thesis using assms proof(cases x)
      case (N x1)
      have g1:"?M1=tm_set 2 (canrepr x1)" by (simp add: A N)
      have g2:"2<length tps"using Assign_vname.prems(2) asm6 by linarith
      then have g3:"clean_tape (tps!2)" by (simp add: Assign_vname.prems(2) Assign_vname.prems(6))
      have "prog (idd) \<turnstile> tps \<sim> s" using Assign_vname.prems(4) by blast
      then have "Max (idd ` var_set prog)+1 < length tps \<and>
     (\<forall>v \<in> var_set prog. v-(idd) \<turnstile> tps \<sim> s)\<and>
   tps!0=(\<lfloor>0\<rfloor>\<^sub>N, 1) \<and>  tps!1=(\<lfloor>0\<rfloor>\<^sub>N, 1) \<and> tps!2=(\<lfloor>0\<rfloor>\<^sub>N, 1) \<and>  tps!(length tps -1)=(\<lfloor>0\<rfloor>\<^sub>N, 1) "by simp
      then have g10:"tps! 2 =(\<lfloor>0\<rfloor>\<^sub>N,1)" by blast
      then have g4:"tps ::: 2 =\<lfloor>0\<rfloor>\<^sub>N" by simp
      have g5:"proper_symbols (canrepr 0)" by simp
      have g6:"proper_symbols (canrepr x1)" by (simp add: proper_symbols_canrepr)
      let ?yt= "8 + tps :#: 2 +  2 * length (canrepr 0) +  Suc (2 * length (canrepr x1))"
      have g8:"canrepr 0 =[]" by (simp add: canrepr_0)
      have g7:"length (canrepr 0) =0" by simp
      then have "?yt=8 + tps :#: 2 +  Suc (2 * length (canrepr x1))" by auto
      then have "?yt=10 +2 * length (canrepr x1)" using g10 
      by (simp add: add.assoc add_Suc_shift eval_nat_numeral(3) numeral_Bit0 numeral_Bit1 snd_conv)
      let ?tps'= "tps[2:=(\<lfloor>x1\<rfloor>\<^sub>N,1)]" 
      have "transforms ?M1 tps ?yt ?tps'"using g1 g2 g3 g4 g5 g6 transforms_tm_setI by presburger
      then show ?thesis sorry
    next
      case (V vv)
      have ff:"prog=(v::=A (V vv))" by (simp add: V \<open>prog = v ::= A x\<close>)
      then have "var_set prog =({v} \<union> (var_set_of_aexp (A (V vv))))" by simp
      then have "var_set prog ={v} \<union>  {vv} " by simp
      then have g7:"vv\<in>var_set prog" by simp
      have g1:"?M1=tm_cp_until (idd vv) 2 {\<box>};;tm_cr (idd vv);;tm_cr 2" by (simp add: A V)
      let ?M11="tm_cp_until (idd vv) 2 {\<box>}"
      let ?M12="tm_cr (idd vv)"
      let ?M13="tm_cr 2"  
      let ?n1= "length (canrepr (s vv))"
      have g3:" tps:::(idd vv) = \<lfloor>s vv\<rfloor>\<^sub>N "sorry
      have g5:" rneigh (tps! (idd vv))  {\<box>} ?n1" sorry
      let ?tps11="tps[(idd vv) := tps ! (idd vv) |+| ?n1, 2 := implant (tps ! (idd vv)) (tps ! 2) ?n1]"
      let ?t1= "Suc ?n1"
      have " inj idd \<and> (\<forall>x\<in>var_set prog. 3 \<le> idd x \<and> idd x + 1 < k)" using Assign_vname.prems(3) by blast
      then have g6:"(idd vv)<length tps"using  Assign_vname.prems(3) using Assign_vname.prems(2) add_lessD1 by (meson g7)

      have g4:"transforms ?M11 tps ?t1 ?tps11" using transforms_tm_cp_untilI g3 g5
      by (smt (verit, best) Assign_vname.prems(2) Assign_vname.prems(3) Suc_1 g7  g6 less_add_one less_trans_Suc neq0_conv not_numeral_le_zero numeral_1_eq_Suc_0 numerals(1))
(*
lemma transforms_tm_crI [transforms_intros]:
  assumes "j < length tps"
    and "clean_tape (tps ! j)"
    and "t = tps :#: j + 2"
    and "tps' = tps[j := tps ! j |#=| 1]"
  shows "transforms (tm_cr j) tps t tps'"
  unfolding tm_cr_def by (tform tps: assms)
*)
    have "clean_tape (tps!(idd vv))" using Assign_vname.prems(2) Assign_vname.prems(6) g6 by blast
    then have g10:"clean_tape (?tps11!(idd vv))" 
    by (smt (verit) clean_tape_ncontents g3 g6 implant_self length_list_update nth_list_update_eq nth_list_update_neq)
    let ?t2= "?tps11:#:(idd vv) + 2"
    let ?tps12 = "?tps11[(idd vv):=?tps11!(idd vv) |#=| 1]" 
    have "length tps =length ?tps11" by auto
    then have "idd vv <length ?tps11" using g6 by linarith
    then have g11:"transforms ?M12 ?tps11 ?t2 ?tps12" using transforms_tm_crI g10 by blast
(*
 assumes "j < length tps"
    and "clean_tape (tps ! j)"
    and "t = tps :#: j + 2"
    and "tps' = tps[j := tps ! j |#=| 1]"
  shows "transforms (tm_cr j) tps t tps'"
*)
    have g12:"2<length ?tps12" using Assign_vname.prems(2) asm6 by auto
    have "clean_tape (tps ! 2)\<and>clean_tape (tps ! (idd vv))" using Assign_vname.prems(6) asm6 
    using \<open>clean_tape (tps ! idd vv)\<close> by auto
    have g13:"clean_tape (?tps11 ! 2)" sorry
    let ?t3 ="?tps12:#:2+ 2" 
    let ?tps13="?tps12[2 := ?tps12 !2 |#=| 1]"
    have "transforms ?M13 ?tps12 ?t3 ?tps13"using g13 
    by (smt (z3) add.commute clean_tape_ncontents fst_conv g12 g3 implant_self length_list_update nth_list_update_eq nth_list_update_neq transforms_tm_crI)

    then have "transforms ?M1 tps (?t1+?t2+?t3) ?tps13" using g11 g4 transforms_turing_machine_sequential by (smt (verit, ccfv_SIG) g1)
    then show ?thesis sorry
    qed
*)

end