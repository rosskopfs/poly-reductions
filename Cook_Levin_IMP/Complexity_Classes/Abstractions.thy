\<^marker>\<open>creator Bilel Ghorbel\<close>
chapter \<open>Abstractions over IMP-\<close>
paragraph \<open>Summary\<close>
text \<open>We define an abstraction layer over our computation model 
      to be able to define complexity classes easily.\<close>
theory Abstractions
  imports  "IMP_Minus.Big_StepT"
begin
paragraph \<open>Definitions\<close>
text \<open>
\<bullet> Formal Languages
\<bullet> Computing a certain result for a certain input
\<bullet> Decider program for a language
\<bullet> Verifier program for a language
\<close>
type_synonym lang = "nat set"

subsection \<open>Computing\<close>
paragraph \<open>Definition\<close>
text \<open>
For rs , xs lists of (register name, value) pairs,
A program c computes for an input xs a result rs, if given that xs is a (eventually partial)
description of the initial state, the computation always terminates with some state s.t. rs a 
description of the final state.  
.\<close>

definition comp :: "com \<Rightarrow> (vname * val) list \<Rightarrow> (vname *val) list \<Rightarrow> bool" where
"comp c input result \<equiv> 
    distinct (map fst input) \<and>
    (\<forall>s. map (s o fst) input  = map snd input \<longrightarrow> 
                      (\<exists>t s'. (c,s) \<Rightarrow>\<^bsup>t\<^esup> s' \<and> map (s' o fst) result  = map snd result ))"

fun state_maker :: "(vname*val) list \<Rightarrow> state \<Rightarrow> state" where 
"state_maker [] s = s"|
"state_maker ((name,value)#l) s = state_maker l (s (name:=value))"

lemma state_maker_works_helper1:
  "\<lbrakk> v \<notin> fst ` set l\<rbrakk> \<Longrightarrow>  state_maker l (sa(v := x)) v = x "
  apply (induction l arbitrary:sa)
   apply (auto simp add: fun_upd_twist)
  done
    
lemma state_maker_works_helper2:
"\<lbrakk>distinct (map fst l); (aa, ba) \<in> set l \<rbrakk> \<Longrightarrow> state_maker l s aa = ba"
   apply (induction l arbitrary:s)
   apply (auto simp add: fun_upd_twist state_maker_works_helper1)
  done  

lemma state_maker_works:
  assumes "distinct (map fst l)"
  assumes "s' = state_maker l s"
  shows "map (s' o fst) l = map snd l"
  using assms
  apply (induction l arbitrary:s')
  apply (auto simp add:state_maker_works_helper1 state_maker_works_helper2)
  done
paragraph \<open>Computing determinism\<close>
text \<open>Thanks to the determinism of IMP-, computations are deterministic.
i.e. if a program c computes for every input xs, two results r1 AND r2 who describe the same
final registers, then r1=r2

comp c is a relation over (partial) register descriptions.
 \<close>
lemma comp_det: 
  assumes "comp c input result" "comp c input result'"
          "map fst result = map fst result'"
  shows "map snd result = map snd result'"
proof -
  obtain s where s_def: "s = state_maker input <>" by blast
  have s_prop:"map (s o fst) input = map snd input" 
      using s_def assms(1) comp_def state_maker_works by simp
  obtain s1 where s1_def : "\<exists>t. (c, s) \<Rightarrow>\<^bsup>t\<^esup> s1" "map (s1 o fst) result = map snd result"
    using assms(1) s_prop comp_def by metis
  obtain s2 where s2_def : "\<exists>t. (c, s) \<Rightarrow>\<^bsup>t\<^esup> s2" "map (s2 o fst) result' = map snd result'"
    using assms(2) s_prop comp_def by metis 
  have "s1 = s2" using s1_def(1) s2_def(1) big_step_t_determ2 by blast
  thus ?thesis using s1_def(2) s2_def(2) assms(3) by (metis map_map) 
qed

paragraph \<open>Computing: composition and sequencing\<close>
text \<open> By sequencing two codes, we compose the relations.\<close>
lemma comp_comp:
  assumes "comp f xs ys" "comp g ys zs"
  shows "comp (f;;g) xs zs"
proof (auto simp add:comp_def)
  show "distinct (map fst xs)" using assms(1) comp_def by auto
next
  fix s
  assume asm:" \<forall>x\<in>set xs. s (fst x) = snd x"
  obtain tf sf where tsf_def: "(f, s) \<Rightarrow>\<^bsup> tf \<^esup> sf" "map (sf o fst) ys  = map snd ys"
    using assms(1) comp_def asm by auto
  obtain tg sg where tsg_def: "(g, sf) \<Rightarrow>\<^bsup> tg \<^esup> sg" "map (sg o fst) zs = map snd zs" 
    using assms(2) comp_def tsf_def(2) by blast
  have " (f;; g, s) \<Rightarrow>\<^bsup> tf+tg\<^esup> sg" using tsf_def(1) tsg_def(1) by blast
  thus " \<exists>t s'. (f;; g, s) \<Rightarrow>\<^bsup> t \<^esup> s' \<and> (\<forall>x\<in>set zs. s' (fst x) = snd x) "
    using tsg_def(2) by auto
qed

paragraph \<open>Register conventions\<close>

text \<open>
\<bullet> The input for a program (independently of its purpose e.g: 
computing a function, decision, verification) is expected to be in the register called ''input''
\<bullet> The certificate (if needed) is expected to be found in the register ''certificate''
\<bullet> The output/result/main result is expected to be found in the same register as the input.
This allows to easily compose to obtain computing code of the composition of computable functions
just by sequencing their computing codes
\<bullet> If not otherwise mentioned, the input is strictly the inital content of the ''input'' register.
In some particular contexts in the theory, we might consider the certificate as second input.
But this will be explicitly mentioned.
\<close>

paragraph \<open>Abreviations according to register conventions\<close>

definition comp' :: "com \<Rightarrow> val \<Rightarrow> val \<Rightarrow> bool" where 
"comp' c x r \<equiv> comp c [(''input'',x)] [(''input'',r)]" 

definition verif :: "com \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val \<Rightarrow> bool" where 
"verif c x z r \<equiv> comp c [(''input'',x),(''certificate'',z)] [(''input'',r)]"


lemma comp'_comp':
  assumes "comp' f x y" "comp' g y z"
  shows "comp' (f;;g) x z"
  using assms unfolding comp'_def
  by(rule comp_comp[where ys="[(''input'',y)]"])

subsection \<open>Decision problems\<close>
paragraph \<open>Convention\<close>
text \<open>Decision programs are programs that compute a boolean logical result 
(hence a decision) given an input.
IMP- does only support natural number values. But we can make our own interpretation of the result
r::nat as a boolean value. 

Theoretically, every predicate in HOL over the result r is an admissible interpretation.
Yet we choose the following convention from now on:
\<bullet> the result r is interpreted as True iff. r = 0

This convention goes in sync with our semantics that check for equality to 0 exclusively 
for branching conditions.

Generally programming languages tend to interpret non-zero values as True rather than zero.
Yet this a design choice since the negation could be implemented using a constant time program.
To avoid complications for proving Cook-Levin, we use 0 for True and non-zero values for False 
\<close>

paragraph \<open>Deciding a language: definition\<close>
text \<open>A decider for a language L should for every input x, compute a unique result (otherwise 
it is depending on other variables).

The result/decision is True iff x \<in> L .\<close>

definition decides :: "com \<Rightarrow> lang \<Rightarrow> bool" where
  "decides c L  \<equiv> (\<forall>x. \<exists>r. comp' c x r \<and> ( x\<in>L \<longleftrightarrow> r = 0))"


subsection \<open>Verifier programs\<close>
paragraph \<open>Definition\<close>
text \<open>After defining verification on the word/natural number level. We define verification on 
the language level.

A verifier for a language L should return a unique verification result/decision r 
for every combination of input x and certificate z.
This result should say whether this certificate z 
is valid for that input x.(result is to be interpreted as a boolean)

Every input x has at least one corresponding valid certificate iff. x \<in> L\<close>

definition is_verif :: "com \<Rightarrow> lang \<Rightarrow> bool" where
"is_verif c L  \<equiv> (\<forall>x z. \<exists>r. verif c x z r) \<and> (\<forall>x. (x\<in>L \<longleftrightarrow> (\<exists>z. verif c x z 0))) "


lemma is_verifI:
  assumes "\<And>x z. \<exists>r. verif c x z r"
    "\<And>x. x\<in>L \<longleftrightarrow> (\<exists>z. verif c x z 0)"
  shows "is_verif c L"
  using assms unfolding is_verif_def by auto

paragraph \<open>Certificate conserving\<close>
text \<open>The code always terminates with a final state that 
has the same certificate register content as the initial state.\<close> 
definition cons_certif :: "com \<Rightarrow> bool" where
  "cons_certif c = (\<forall>s t s'. (c,s) \<Rightarrow>\<^bsup> t \<^esup> s' \<longrightarrow> s ''certificate'' = s' ''certificate'')"

end  
