\<^marker>\<open>creator Florian Keßler\<close>

section "IMP-- to SAS++ State Translations"

theory IMP_Minus_Minus_To_SAS_Plus_Plus_State_Translations 
  imports SAS_Plus_Plus IMP_Minus_Minus_Small_StepT
begin

text \<open> We define a translation between IMP-- states and SAS++ states. For this purpose, it is useful
      to think of IMP-- states as not only a map from registers to bits, but rather a pair of a 
      computation and such a map. The translated SAS++ states is a map assigning the computation
      to the special variable PC, and otherwise mapping register names to the bit values they
      had in the original IMP-- state. \<close>

datatype domain_element = EV bit | PCV com

datatype variable = VN vname | PC

type_synonym sas_state = "(variable, domain_element) State_Variable_Representation.state"
type_synonym imp_state = state

definition imp_minus_state_to_sas_plus :: "(com \<times> imp_state) \<Rightarrow> sas_state" where
"imp_minus_state_to_sas_plus ci = ((\<lambda>x. Some (EV x)) \<circ>\<^sub>m (snd ci)
  \<circ>\<^sub>m (\<lambda>x. (case x of VN v \<Rightarrow> Some v)))
  (PC \<mapsto> PCV (fst ci))"


definition sas_plus_state_to_imp_minus:: "sas_state \<Rightarrow> (com \<times> imp_state)" where
"sas_plus_state_to_imp_minus ss = ((case (the (ss PC)) of (PCV c) \<Rightarrow> c), 
  (\<lambda>x. (case x of EV y \<Rightarrow> Some y | _ \<Rightarrow> None)) \<circ>\<^sub>m ss \<circ>\<^sub>m (\<lambda>x. Some (VN x)))"

definition sane_sas_plus_state:: "sas_state \<Rightarrow> bool" where
"sane_sas_plus_state ss \<equiv> (\<exists>x. ss PC = Some (PCV x)) \<and> 
  (\<forall>v. VN v \<in> dom ss \<longrightarrow> (\<exists>x. ss (VN v) = Some (EV x)))"

lemma sas_plus_state_to_imp_minus_imp_minus_state_to_sas_plus[simp]:
  "sas_plus_state_to_imp_minus (imp_minus_state_to_sas_plus (c, is)) = (c, is)" 
proof -
  have "(snd (sas_plus_state_to_imp_minus (imp_minus_state_to_sas_plus (c, is)))) x = is x" for x
    by (auto simp: imp_minus_state_to_sas_plus_def sas_plus_state_to_imp_minus_def 
        map_comp_def option.case_eq_if)
  then show ?thesis
    by (auto simp: imp_minus_state_to_sas_plus_def sas_plus_state_to_imp_minus_def)
qed

lemma imp_minus_state_to_sas_plus_sas_plus_state_to_imp_minus[simp]: 
  assumes "sane_sas_plus_state ss "
  shows "imp_minus_state_to_sas_plus (sas_plus_state_to_imp_minus ss) = ss" 
proof -
  have "(imp_minus_state_to_sas_plus (sas_plus_state_to_imp_minus ss)) x = ss x" for x using assms
    by (fastforce simp: imp_minus_state_to_sas_plus_def sas_plus_state_to_imp_minus_def 
        sane_sas_plus_state_def option.case_eq_if map_comp_def split: variable.splits)
  then show ?thesis by (auto simp: imp_minus_state_to_sas_plus_def sas_plus_state_to_imp_minus_def)
qed

lemma imp_minus_state_to_sas_plus_of_same_c_eq_iff[simp]: 
  "(imp_minus_state_to_sas_plus (c, s1) = imp_minus_state_to_sas_plus (c, s2))
  \<longleftrightarrow> s1 = s2" 
proof
  assume a: "imp_minus_state_to_sas_plus (c, s1) = imp_minus_state_to_sas_plus (c, s2)"
  have "\<forall>v. (s1 v = s2 v)"
  proof (rule ccontr)
    assume "\<not> (\<forall>v. s1 v = s2 v)"
    then obtain v where "s1 v \<noteq> s2 v" by blast
    then have "imp_minus_state_to_sas_plus (c, s1) (VN v) \<noteq> imp_minus_state_to_sas_plus (c, s2) (VN v)"
      by (auto simp: imp_minus_state_to_sas_plus_def map_comp_def domD domIff split: option.splits)
    then show "False" using a by simp
  qed
  then show "s1 = s2" by auto
qed auto

lemma snd_sas_plus_state_to_imp_minus_updated[simp]: 
  "snd (sas_plus_state_to_imp_minus
                ((imp_minus_state_to_sas_plus (c, is))(VN x \<mapsto> y)))
    = is(x := (case y of EV y' \<Rightarrow> Some y' | _ \<Rightarrow> None))"
  by (auto simp: imp_minus_state_to_sas_plus_def sas_plus_state_to_imp_minus_def 
       Let_def map_comp_def option.case_eq_if)

lemma imp_minus_state_to_sas_plus_PC[simp]: 
  "(imp_minus_state_to_sas_plus (c1, is)) PC = Some (PCV c1)" 
  by (simp add: imp_minus_state_to_sas_plus_def)

lemma imp_minus_state_to_sas_plus_VN_Some_iff[simp]: 
  "(imp_minus_state_to_sas_plus (c, is) (VN x) = Some (EV y)) 
  \<longleftrightarrow> (is x = Some y)"
  by(auto simp: imp_minus_state_to_sas_plus_def map_comp_Some_iff)

lemma imp_minus_state_to_sas_plus_eq_Some_non_zero_iff[simp]: 
  "imp_minus_state_to_sas_plus (c, is) (VN x) = Some y \<Longrightarrow>
       (y \<noteq> EV (Num 0)) \<longleftrightarrow> (is x \<noteq> Some (Num 0))"
  by(auto simp: imp_minus_state_to_sas_plus_def map_comp_Some_iff)

lemma imp_minus_state_to_sas_plus_map_le_then: "imp_minus_state_to_sas_plus (c, I) \<subseteq>\<^sub>m I' 
  \<Longrightarrow> I \<subseteq>\<^sub>m snd (sas_plus_state_to_imp_minus I')"
  apply(auto simp: imp_minus_state_to_sas_plus_def sas_plus_state_to_imp_minus_def)
   apply(simp add: map_le_def map_comp_def)
   apply(auto split: option.splits domain_element.splits)
     apply (metis domIff option.distinct option.simps variable.simps)
   apply (metis domI domain_element.inject option.inject option.simps variable.distinct variable.simps)
  by (metis (mono_tags, lifting) domI domain_element.distinct option.inject option.simps 
      variable.distinct variable.simps)


lemma map_of_map_VN_EV: "map_of (map (\<lambda>v. (VN v, EV y)) vs) (VN a) = 
  map_option EV (map_of (map (\<lambda>v. (v, y)) vs) a)"
  apply(induction vs) by auto

lemma map_leq_imp_minus_state_to_sas_plus_iff: 
  "(map_of (map (\<lambda>v. (VN v, EV y)) vs))(PC \<mapsto> PCV c) \<subseteq>\<^sub>m imp_minus_state_to_sas_plus (c, is)
  \<longleftrightarrow> map_of (map (\<lambda>v. (v, y)) vs) \<subseteq>\<^sub>m is"
  by(auto simp: imp_minus_state_to_sas_plus_def map_le_def map_comp_def map_of_SomeD 
      dom_map_of_conv_image_fst map_of_map_VN_EV split: option.splits)

lemma dom_snd_sas_plus_state_to_imp_minus:  "sane_sas_plus_state ss 
  \<Longrightarrow> dom (snd (sas_plus_state_to_imp_minus ss)) 
  = { v |v. VN v \<in> dom ss }" 
  by(fastforce simp: sane_sas_plus_state_def sas_plus_state_to_imp_minus_def map_comp_Some_iff 
      split: option.splits)
  

end