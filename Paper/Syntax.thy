theory Syntax
  imports "IMP_To_IMP-.IMP_To_IMP_Minus" "IMP.IMP_Tailcall" "IMP-.IMP_Minus_Big_StepT"
begin

abbreviation "omax \<equiv> max"

abbreviation "R\<equiv>V"
abbreviation "C\<equiv>N"

bundle atom begin
  notation atomVal ("\<lbrakk>(_)\<rbrakk> \<^sub>_")
end
unbundle atom

notation aval ("\<lbrakk>(_)\<rbrakk> \<^sub>_")

bundle aops begin
notation Plus ("_ + _")
notation Sub ("_ - _")
end
unbundle aops

no_notation big_step_t ("_ \<Rightarrow>\<^bsup> _ \<^esup> _" 55)

abbreviation bsle ("_ \<Rightarrow>\<^bsup>_\<^esup> _") where 
  "bsle ps n s' \<equiv> \<exists>n'. n' \<le> n \<and> big_step_t ps n' s'"
bundle imp
begin
notation bsle ("_ \<Rightarrow>\<^bsup>_\<^esup> _")
end
unbundle imp

notation max_const ("_\<^bsub>max\<^esub>")
abbreviation smax ("_\<^bsub>max \<^esub>") where 
  "smax s \<equiv> Max (range s)"
notation Max ("max")

abbreviation "RECURSE\<equiv>tTAIL"
abbreviation "rets ps r n v \<equiv> (\<exists>s' n'. n' \<le> n \<and> big_step_t ps n' s' \<and> s' r = v)"
bundle total begin
notation rets ("_ \<Rightarrow>\<^sub>_\<^bsup>_\<^esup> _")
end
unbundle total

no_notation tbig_step_t ("_ \<turnstile> _ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
abbreviation "tbst p ps n s' \<equiv> \<exists>n'. n' \<le> n \<and> tbig_step_t p ps n' s'"
notation tbst ("_ \<turnstile> _ \<Rightarrow>\<^bsup>_\<^esup>  _")


no_notation tail_step ("\<turnstile>_ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)

abbreviation "tsbe ps n s' \<equiv> \<exists>n'. n' \<le> n \<and> tail_step ps n' s'"
bundle tail begin
notation tsbe ("_ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
end

bundle holb begin
notation True ("\<one>")
notation False ("\<zero>")
end
unbundle holb

bundle bitsb begin
notation One ("\<one>")
notation Zero ("\<zero>")
end

no_notation tail_steps ("_ \<turnstile>''_ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
abbreviation "tssbe p ps n s' \<equiv> \<exists>n'. n' \<le> n \<and> tail_steps p ps n' s'"

bundle tails begin
notation tssbe ("_ \<turnstile>''_ \<Rightarrow>\<^bsup>_\<^esup>  _")
end

notation compile ("\<lparr>_\<rparr>\<^sub>\<circle>")

abbreviation 
  "retsS p ps r n s \<equiv> (\<exists>s'. \<exists>n' \<le> n. tbig_step_t p ps n' s' \<and> (s' = s on set r))"
abbreviation  
  "retsS2 ps r n s \<equiv> (\<exists>s'. \<exists>n' \<le> n. big_step_t' ps n' s' \<and> (s' = s on set r))"

bundle partial begin
notation retsS ("_ \<turnstile> _ \<Rightarrow>\<^bsub>_\<^esub>\<^bsup>_\<^esup> _")
notation retsS2 ("_ \<Rightarrow>\<^bsub>_\<^esub>\<^bsup>_\<^esup> _")
end

abbreviation "regs\<equiv>vars"
abbreviation subs1 ("_['(_ x')'/x]") where "subs1 p m \<equiv> subst m p"

notation inline ("\<lparr>_\<rparr>\<^sub>\<star>")

abbreviation "retsS3 ps r n s \<equiv> (\<exists>s'. \<exists>n' \<le> n. big_step_t ps n' s' \<and> (s' = s on set r))"

bundle partial2 begin
notation retsS3 ("_ \<Rightarrow>\<^bsub>_\<^esub>\<^bsup>_\<^esup> _")
end

notation size\<^sub>c ("\<bar>_\<bar>")
unbundle no abs_syntax

abbreviation asstobin ("\<lparr>_\<rparr>\<^sup>_\<^bsub>_\<^esub>") where "asstobin a w r \<equiv> assignment_to_binary w r a"
abbreviation sttobin ("\<lparr>_\<rparr>\<^sup>_") where "sttobin s w \<equiv> IMP_State_To_IMP_Minus s w"
abbreviation ptobin ("\<lparr>_\<rparr>\<^sup>_") where "ptobin p w \<equiv> IMP_To_IMP_Minus p w"

unbundle no imp_minus_big

abbreviation bst where "bst ps n s' \<equiv>  (\<exists>n'. n' \<le> n \<and> big_step ps n' s')"
bundle minus begin
notation bst ("_ \<Rightarrow>\<^bsup>_\<^esup> _")
end



end