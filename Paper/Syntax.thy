theory Syntax
  imports "IMP_To_IMP-.IMP_To_IMP_Minus" "IMP.IMP_Tailcall" "IMP-.IMP_Minus_Big_StepT"
    "HOL_Nat_To_IMP-.IMP_Terminates_With"
begin

(* disabled: original syntax *)

unbundle no big_step_syntax
unbundle no tbig_step_syntax
no_notation tail_step ("\<turnstile>_ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
no_notation big_step ("_ \<Rightarrow>\<^bsup>_\<^esup> _" 55)
no_notation big_step_t ("_ \<Rightarrow>\<^bsup> _ \<^esup> _" 55)
no_notation tail_steps ("_ \<turnstile>''_ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)

(* terminates with syntax *)
bundle terminates_with_syntax
begin
  notation terminates_with_res_IMP_Minus ("'(_, _') \<Rightarrow>\<^bsub>_\<^esub> _")
  notation terminates_with_res_IMP_Tailcall ("_ \<turnstile> '(_, _') \<Rightarrow>\<^bsub>_\<^esub> _")
  notation terminates_with_IMP_Tailcall ("_ \<turnstile> '(_, _') \<Rightarrow> _")
end

(* enabled: canonical *)

abbreviation "omax \<equiv> max"
abbreviation "R\<equiv>V"
abbreviation "C\<equiv>N"
notation aval ("\<lbrakk>(_)\<rbrakk> \<^sub>_")
notation max_const ("_\<^bsub>max\<^esub>")
abbreviation smax ("_\<^bsub>max \<^esub>") where "smax s \<equiv> Max (range s)"
notation Max ("max")
abbreviation "RECURSE\<equiv>tTAIL"
abbreviation "regs\<equiv>vars"
abbreviation subs1 ("_['(_ x')'/x]") where "subs1 p m \<equiv> subst m p"
notation size\<^sub>c ("\<bar>_\<bar>")
unbundle no abs_syntax
notation compile ("\<lparr>_\<rparr>\<^sub>\<circle>")
notation inline ("\<lparr>_\<rparr>\<^sub>\<star>")


(* abbrevs for context-dependent bundles *)

abbreviation bsle where "bsle ps n s' \<equiv> \<exists>n'. n' \<le> n \<and> big_step_t ps n' s'"
abbreviation "rets ps r n v \<equiv> (\<exists>s'. big_step_t ps n s' \<and> s' r = v)"
abbreviation "tbst p ps n s' \<equiv> \<exists>n'. n' \<le> n \<and> tbig_step_t p ps n' s'"
abbreviation "tsbe ps n s' \<equiv> tail_step ps n s'"
abbreviation "tssbe p ps n s' \<equiv> \<exists>n'. n' \<le> n \<and> tail_steps p ps n' s'"
abbreviation "retsS p ps r n s \<equiv> (\<exists>s'. \<exists>n' \<le> n. tbig_step_t p ps n' s' \<and> (s' = s on set r))"
abbreviation "retsS2 ps r n s \<equiv> (\<exists>s'. \<exists>n' \<le> n. big_step_t' ps n' s' \<and> (s' = s on set r))"
abbreviation "retsS3 ps r n s \<equiv> (\<exists>s'. \<exists>n' \<le> n. big_step_t ps n' s' \<and> (s' = s on set r))"
abbreviation "bst ps n s' \<equiv>  (\<exists>n'. n' \<le> n \<and> big_step ps n' s')"
abbreviation asstobin ("\<lparr>_\<rparr>\<^sup>_\<^bsub>_\<^esub>") where "asstobin a w r \<equiv> assignment_to_binary w r a"
abbreviation sttobin ("\<lparr>_\<rparr>\<^sup>_") where "sttobin s w \<equiv> IMP_State_To_IMP_Minus s w"
abbreviation ptobin ("\<lparr>_\<rparr>\<^sup>_") where "ptobin p w \<equiv> IMP_To_IMP_Minus p w"


(* bundles *)

bundle atom begin
  notation atomVal ("\<lbrakk>(_)\<rbrakk> \<^sub>_")
end

bundle aops begin
  notation Plus ("_ + _")
  notation Sub ("_ - _")
end

bundle orig begin
notation big_step_t ("_ \<Rightarrow>\<^bsup>_\<^esup> _")
notation tbig_step_t ("_ \<turnstile> _ \<Rightarrow>\<^bsup>_\<^esup>  _")
end

bundle imp begin
  notation bsle ("_ \<Rightarrow>\<^bsup>_\<^esup> _")
  notation tbst ("_ \<turnstile> _ \<Rightarrow>\<^bsup>_\<^esup>  _")
end

bundle tail begin
  notation tsbe ("_ \<Rightarrow>\<^bsup>_\<^esup>  _" 55)
end

bundle tails begin
  notation tssbe ("_ \<turnstile>''_ \<Rightarrow>\<^bsup>_\<^esup>  _")
end

bundle partial begin
  notation rets ("_ \<Rightarrow>\<^sub>_\<^bsup>_\<^esup> _")
  notation retsS ("_ \<turnstile> _ \<Rightarrow>\<^bsub>_\<^esub>\<^bsup>_\<^esup> _")
  notation retsS2 ("_ \<Rightarrow>\<^bsub>_\<^esub>\<^bsup>_\<^esup> _")
  notation retsS3 ("_ \<Rightarrow>\<^bsub>_\<^esub>\<^bsup>_\<^esup> _")
end

bundle minus begin
  notation big_step ("_ \<Rightarrow>\<^bsup>_\<^esup> _")
end

bundle minus2 begin
  notation bst ("_ \<Rightarrow>\<^bsup>_\<^esup> _")
end

bundle holb begin
  notation True ("\<one>")
  notation False ("\<zero>")
end

bundle bitsb begin
  notation One ("\<one>")
  notation Zero ("\<zero>")
end

end
