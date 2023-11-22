\<^marker>\<open>creator Bilel Ghorbel, Florian Kessler\<close>

section "IMP-- An even more reduced imperative language"

theory IMP_Minus_Minus_Com imports Main begin

paragraph "Summary"
text\<open>Syntax definition for IMP--. Based on the syntax definition of IMP-. Compared to IMP-, 
  we get rid of arithmetic expressions. Instead, we can only assign bit values to registers. 
  For the IF and WHILE conditions, we add the possibility to specify a list of registers, such that
  the condition is considered True if at least one of the registers is non-zero. \<close>

datatype bit = Zero | One

fun nat_to_bit:: "nat \<Rightarrow> bit" where
"nat_to_bit 0 = Zero" |
"nat_to_bit _ = One" 

lemma bit_neq_zero_iff[simp]: "x \<noteq> Zero \<longleftrightarrow> x = One" by (cases x) auto
lemma bit_neq_one_iff[simp]: "x \<noteq> One \<longleftrightarrow> x = Zero" by (cases x) auto

lemma nat_to_bit_eq_One_iff: "nat_to_bit x = One \<longleftrightarrow> x > 0" 
  by (cases x) auto

lemma nat_to_bit_eq_One_iff': "One = nat_to_bit x \<longleftrightarrow> x > 0" 
  by (cases x) auto

lemma nat_to_bit_eq_Zero_iff: "nat_to_bit x = Zero \<longleftrightarrow> x = 0" 
  by (cases x) auto

lemma nat_to_bit_eq_Zero_iff': "Zero = nat_to_bit x \<longleftrightarrow> x = 0" 
  by (cases x) auto

lemmas nat_to_bit_cases = nat_to_bit_eq_One_iff nat_to_bit_eq_One_iff' nat_to_bit_eq_Zero_iff
  nat_to_bit_eq_Zero_iff'

type_synonym vname = string

datatype
  com = SKIP
  | Assign vname bit
  | Seq com com         
  | If "(vname list)" com com     
  | While "(vname list)" com         

bundle com_syntax
begin
notation Assign ("_ ::= _" [1000, 61] 61) and
         Seq ("_;;/ _"  [60, 61] 60) and
         If ("(IF _/\<noteq>0 THEN _/ ELSE _)"  [0, 0, 61] 61) and
         While ("(WHILE _/\<noteq>0 DO _)"  [0, 61] 61)
end

bundle no_com_syntax
begin
no_notation Assign ("_ ::= _" [1000, 61] 61) and
            Seq ("_;;/ _"  [60, 61] 60) and
            If ("(IF _/\<noteq>0 THEN _/ ELSE _)"  [0, 0, 61] 61) and
            While ("(WHILE _/\<noteq>0 DO _)"  [0, 61] 61)
end

unbundle com_syntax

end