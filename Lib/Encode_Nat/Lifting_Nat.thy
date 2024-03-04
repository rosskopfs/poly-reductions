theory Lifting_Nat
  imports
    Main
    "HOL-Library.Nat_Bijection"
    "HOL-Library.Simps_Case_Conv"
    Encode_Nat
begin

section \<open>Lifting from \<^typ>\<open>bool\<close>\<close>


lemma Domainp_nat_bool_rel[transfer_domain_rule]:
  "Domainp (cr_nat :: _ \<Rightarrow> bool \<Rightarrow> _) = (\<lambda>x. x = False_nat \<or> x = True_nat)"
  unfolding cr_nat_def Abs_nat_bool.simps
  by (auto split:bool.split)

context includes lifting_syntax
begin


lemma nat_bool_rel_conj[transfer_rule]:
  "(cr_nat ===> cr_nat ===> cr_nat) max (\<and>)"
  unfolding cr_nat_def Abs_nat_bool.simps
  by (simp add: pair_def False_nat_def True_nat_def prod_encode_def rel_fun_def split:bool.splits)

lemma nat_bool_rel_disj[transfer_rule]:
  "(cr_nat ===> cr_nat ===> cr_nat) min (\<or>)"
  unfolding cr_nat_def Abs_nat_bool.simps
  by (simp add: pair_def False_nat_def True_nat_def prod_encode_def rel_fun_def split:bool.splits)


end

schematic_goal
  shows "cr_nat ?t (a \<and> (b \<or> c))"
  apply transfer_prover_start
       apply transfer_step+
  apply (rule HOL.refl)
  done



fun rev_tr :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rev_tr acc [] = acc"
| "rev_tr acc (x # xs) = rev_tr (x # acc) xs"

case_of_simps rev_tr_case_def: rev_tr.simps

\<comment> \<open>Can be lifted with Kevin's transport framework\<close>
definition rev_tr_nat :: "'a::lift_nat itself \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "rev_tr_nat _ acc xs \<equiv> (Abs_nat :: 'a list \<Rightarrow> nat) (rev_tr (Rep_nat acc) (Rep_nat xs))"

datatype_lift_nat option
test2 option

context includes lifting_syntax
begin

\<comment> \<open>
  Needs to be provided by the datatype compiler.
  We probably should introduce definitions for the nat versions of
  each constructor.
\<close>

thm cr_nat_def case_nat_nat_def
lemma cr_nat_nat_case_nat[transfer_rule]:
  "(R ===> (cr_nat ===> R) ===> cr_nat ===> R) case_nat_nat case_nat"
  unfolding cr_nat_def case_nat_nat_def
  using case_nat_eq_if
  by (simp add: rel_fun_def pair_def fstP_def sndP_def zero_nat_def Suc_nat_def Abs_nat_nat.simps split: nat.split)


\<comment> \<open>Needs to be provided by the datatype compiler\<close>


lemma cr_nat_list_case_list[transfer_rule]:
  "(R ===> (cr_nat ===> cr_nat ===> R) ===> cr_nat ===> R) case_list_nat case_list"
  unfolding cr_nat_def case_list_nat_def
  using case_list_eq_if
  by (simp add: rel_fun_def pair_def fstP_def sndP_def Nil_nat_def Cons_nat_def Abs_nat_list.simps split: list.split)

\<comment> \<open>Can be proved with Kevin's transport framework\<close>

lemma rev_tr_nat_lifting[transfer_rule]:
  includes lifting_syntax
  shows "(cr_nat ===> cr_nat ===> cr_nat) (rev_tr_nat TYPE('a::lift_nat)) (rev_tr :: 'a list \<Rightarrow> _)"
  unfolding rev_tr_nat_def cr_nat_def
  by(simp add: rel_fun_def)


end

schematic_goal rev_tr_nat_synth:
  assumes [transfer_rule]: "(cr_nat :: nat \<Rightarrow> 'a list \<Rightarrow> bool) accn (Rep_nat accn)"
  assumes [transfer_rule]: "(cr_nat :: nat \<Rightarrow> 'a list \<Rightarrow> bool) xsn (Rep_nat xsn)"
  shows "cr_nat ?t ((rev_tr :: 'a::lift_nat list \<Rightarrow> _) (Rep_nat accn) (Rep_nat xsn))"
  apply (subst rev_tr_case_def)
  apply transfer_prover_start
        apply transfer_step+
  apply (rule HOL.refl)
  done

lemma rev_tr_nat_synth_def:
  fixes acc :: "'a::lift_nat list" and xs :: "'a list"
  assumes "accn = Abs_nat acc"
  assumes "xsn = Abs_nat xs"
  shows "rev_tr_nat TYPE('a) accn xsn
    = case_list_nat accn (\<lambda>x3a. rev_tr_nat TYPE('a) (Cons_nat x3a accn)) xsn"
  apply(rule HOL.trans[OF _ rev_tr_nat_synth[unfolded cr_nat_def, symmetric]])
    apply(use assms in \<open>simp_all add: rev_tr_nat_def\<close>)
  done


\<comment> \<open>Final theorem that can be passed to the IMP compiler\<close>
thm rev_tr_nat_synth_def[unfolded case_list_nat_def]



fun elemof :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "elemof _ [] = False"
| "elemof y (x#xs) = (if (y = x) then True else elemof y xs)"

case_of_simps elemof_case_def: elemof.simps

definition elemof_nat :: "'a::lift_nat itself \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "elemof_nat _ x xs \<equiv> (Abs_nat :: bool \<Rightarrow> nat) (elemof ((Rep_nat::nat => 'a) x) (Rep_nat xs))"

lemma elemof_nat_lifting[transfer_rule]:
  includes lifting_syntax
  shows "(cr_nat ===> cr_nat ===> cr_nat) (elemof_nat TYPE('a::lift_nat)) (elemof :: 'a \<Rightarrow> _)"
  unfolding elemof_nat_def cr_nat_def
  by(simp add: rel_fun_def)

schematic_goal elemof_nat_synth:
  assumes [transfer_rule]: "(cr_nat :: nat \<Rightarrow> 'a \<Rightarrow> bool) xn (Rep_nat xn)"
  assumes [transfer_rule]: "(cr_nat :: nat \<Rightarrow> 'a list \<Rightarrow> bool) xsn (Rep_nat xsn)"
  shows "cr_nat ?t ((elemof :: 'a::lift_nat \<Rightarrow> _) (Rep_nat xn) (Rep_nat xsn))"
  apply (subst elemof_case_def)
  apply transfer_prover_start
           apply transfer_step+
  apply (rule HOL.refl)
  done

lemma elemof_nat_synth_def:
  fixes x :: "'a::lift_nat " and xs :: "'a list"
  assumes "xn = Abs_nat x"
  assumes "xsn = Abs_nat xs"
  shows "elemof_nat TYPE('a) xn xsn
    = case_list_nat False_nat (\<lambda>y ys. if xn = y then True_nat else elemof_nat TYPE('a) xn ys) xsn"
  apply(rule HOL.trans[OF _ elemof_nat_synth[unfolded cr_nat_def, symmetric]])
    apply(use assms in \<open>simp_all add: elemof_nat_def\<close>)
  done

thm elemof_nat_synth_def[unfolded case_list_nat_def]

definition If_nat :: "'a::lift_nat itself \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "If_nat _ c t f \<equiv> (Abs_nat :: 'a \<Rightarrow> nat) (If (Rep_nat c) (Rep_nat t) (Rep_nat f))"


lemma cr_nat_bool_case_bool[transfer_rule]:
  includes lifting_syntax
  shows "(cr_nat ===> cr_nat ===> cr_nat ===> cr_nat) case_bool_nat case_bool"
  unfolding cr_nat_def case_bool_nat_def
  by (simp add: rel_fun_def pair_def fstP_def sndP_def False_nat_def True_nat_def Abs_nat_bool.simps split: bool.split)

lemma If_nat_lifting[transfer_rule]:
  includes lifting_syntax
  shows "(cr_nat ===> cr_nat ===> cr_nat ===> cr_nat)
  (If_nat TYPE('a::lift_nat)) (If :: bool \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a)"
  by(simp add: If_nat_def rel_fun_def cr_nat_def)

lemma If_case_def: "If c t f = (case c of True \<Rightarrow> t | False \<Rightarrow> f)" by simp

schematic_goal If_nat_synth:
  assumes [transfer_rule]: "(cr_nat :: nat \<Rightarrow> bool \<Rightarrow> bool) c (Rep_nat c)"
  assumes [transfer_rule]: "(cr_nat :: nat \<Rightarrow> 'a \<Rightarrow> bool) t (Rep_nat t)"
  assumes [transfer_rule]: "(cr_nat :: nat \<Rightarrow> 'a \<Rightarrow> bool) f (Rep_nat f)"
  shows "cr_nat ?t ((If :: bool \<Rightarrow> 'a::lift_nat \<Rightarrow> 'a \<Rightarrow> 'a) (Rep_nat c) (Rep_nat t) (Rep_nat f))"
  apply (subst If_case_def)
  apply transfer_prover_start
      apply transfer_step+
  apply (rule HOL.refl)
  done

lemma If_nat_synth_def:
  fixes c :: "bool" and t :: "'a::lift_nat" and f :: "'a"
  assumes "cn = Abs_nat c"
  assumes "tn = Abs_nat t"
  assumes "fn = Abs_nat f"
  shows "If_nat TYPE('a) cn tn fn = case_bool_nat tn fn cn"
  apply(rule HOL.trans[OF _ If_nat_synth[unfolded cr_nat_def, symmetric]])
  unfolding If_nat_def assms by simp+

thm If_nat_synth_def[unfolded case_bool_nat_def]


fun takeWhile :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "takeWhile P [] = []" |
  "takeWhile P (x # xs) = (if P x then x # takeWhile P xs else [])"

case_of_simps takeWhile_case_def: takeWhile.simps

definition takeWhile_nat :: "'a::lift_nat itself \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "takeWhile_nat _ P xs \<equiv> (Abs_nat :: 'a list \<Rightarrow> nat) (takeWhile (Rep_nat \<circ> P \<circ> Abs_nat) (Rep_nat xs))"

lemma takeWhile_nat_lifting[transfer_rule]:
  includes lifting_syntax
  assumes "(cr_nat ===> cr_nat) P_nat P"
  shows "(cr_nat ===> cr_nat) (takeWhile_nat TYPE('a::lift_nat) P_nat)
  ((takeWhile :: ('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list) P)"
  using assms
  by(simp add: takeWhile_nat_def rel_fun_def comp_def cr_nat_def)


schematic_goal takeWhile_nat_synth:
  includes lifting_syntax
  assumes [transfer_rule]: "(cr_nat :: nat \<Rightarrow> 'a list \<Rightarrow> bool) xsn (Rep_nat xsn)"
  assumes [transfer_rule]:"(cr_nat ===> cr_nat) P_nat P"
  shows "cr_nat ?t ((takeWhile :: ('a::lift_nat \<Rightarrow> bool) \<Rightarrow> _) P (Rep_nat xsn))"
  apply (subst takeWhile_case_def)
  apply transfer_prover_start
          apply transfer_step+
  apply (rule HOL.refl)
  done

lemma takeWhile_nat_synth_def:
  includes lifting_syntax
  fixes P :: "'a::lift_nat \<Rightarrow> bool" and xs :: "'a list"
  assumes "(cr_nat ===> cr_nat) P_nat P"
  assumes "xsn = Abs_nat xs"
  shows "takeWhile_nat TYPE('a) P_nat xsn
    = case_list_nat Nil_nat (\<lambda>x3a x2ba. If_nat TYPE('a list) (P_nat x3a)
          (Cons_nat x3a (takeWhile_nat TYPE('a) P_nat x2ba)) Nil_nat) xsn"
  apply(rule HOL.trans[OF _ takeWhile_nat_synth[unfolded cr_nat_def, symmetric]])
  using assms apply(simp add: takeWhile_nat_def rel_fun_def cr_nat_def)+
  done

thm takeWhile_nat_synth_def[unfolded case_list_nat_def]

fun head :: "'a list \<Rightarrow> 'a" where
  "head [] = undefined" |
  "head (x # _) = x"

case_of_simps head_case_def: head.simps

definition head_nat :: "'a::lift_nat itself \<Rightarrow> nat \<Rightarrow> nat" where
  "head_nat _ xsn \<equiv> (Abs_nat :: 'a \<Rightarrow> nat) (head (Rep_nat xsn))"

lemma head_nat_lifting[transfer_rule]:
  includes lifting_syntax
  shows "(cr_nat ===> cr_nat) (head_nat TYPE('a::lift_nat)) (head :: 'a list \<Rightarrow> _)"
  unfolding head_nat_def cr_nat_def
  by(simp add: rel_fun_def)

schematic_goal head_nat_synth:
  assumes [transfer_rule]: "(cr_nat :: nat \<Rightarrow> 'a list \<Rightarrow> bool) xsn (Rep_nat xsn)"
  shows "cr_nat ?t ((head :: 'a::lift_nat list \<Rightarrow> _) (Rep_nat xsn))"
  apply (subst head_case_def)
  apply transfer_prover_start
     apply transfer_step+
  apply (rule HOL.refl)
  done

lemma head_nat_synth_def:
  fixes xs :: "'a::lift_nat list"
  assumes "xsn = Abs_nat xs"
  shows "head_nat TYPE('a) xsn
    = case_list_nat (Abs_nat (undefined::'a)) (\<lambda>x2a x1a. x2a) xsn"
  apply(rule HOL.trans[OF _ head_nat_synth[unfolded cr_nat_def, symmetric]])
  using assms apply(simp add: head_nat_def rel_fun_def cr_nat_def)+
  done
thm head_nat_synth_def[unfolded case_list_nat_def]

fun append :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "append xs [] = xs" |
  "append xs ys = rev_tr ys (rev_tr [] xs)"


case_of_simps append_case_def: append.simps

definition append_nat :: "'a::lift_nat itself \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "append_nat _ xsn ysn \<equiv> (Abs_nat :: 'a list \<Rightarrow> nat) (append (Rep_nat xsn) (Rep_nat ysn))"

lemma append_nat_lifting[transfer_rule]:
  includes lifting_syntax
  shows "(cr_nat ===> cr_nat ===> cr_nat) (append_nat TYPE('a::lift_nat))
  (append :: 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list)"
  by(simp add: append_nat_def rel_fun_def comp_def cr_nat_def)

schematic_goal append_nat_synth:
  includes lifting_syntax
  assumes [transfer_rule]: "(cr_nat :: nat \<Rightarrow> 'a list \<Rightarrow> bool) xsn (Rep_nat xsn)"
  assumes [transfer_rule]: "(cr_nat :: nat \<Rightarrow> 'a list \<Rightarrow> bool) ysn (Rep_nat ysn)"
  shows "cr_nat ?t ((append :: 'a::lift_nat list \<Rightarrow> _) (Rep_nat xsn) (Rep_nat ysn))"
  apply (subst append_case_def)
  apply transfer_prover_start
          apply transfer_step+
  apply (rule HOL.refl)
  done

lemma append_nat_synth_def:
  fixes xs :: "'a::lift_nat list" and ys :: "'a list"
  assumes "xsn = Abs_nat xs"
  assumes "ysn = Abs_nat ys"
  shows "append_nat TYPE('a) xsn ysn = case_list_nat xsn (\<lambda>x3a x2ba. rev_tr_nat TYPE('a)
                (Cons_nat x3a x2ba) (rev_tr_nat TYPE('a) Nil_nat xsn)) ysn"
  apply(rule HOL.trans[OF _ append_nat_synth[unfolded cr_nat_def, symmetric]])
  using assms apply(simp add: append_nat_def rel_fun_def cr_nat_def)+
  done




fun plus :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "plus m 0 = m" |
  "plus m (Suc n) = Suc (plus m n)"

case_of_simps plus_case_def: plus.simps

definition plus_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "plus_nat m n \<equiv> Abs_nat (plus (Rep_nat m) (Rep_nat n))"

lemma plus_nat_lifting[transfer_rule]:
  includes lifting_syntax
  shows "(cr_nat ===> cr_nat ===> cr_nat) plus_nat plus"
  unfolding plus_nat_def cr_nat_def
  by(simp add: rel_fun_def)

schematic_goal plus_nat_synth:
  assumes [transfer_rule]: "(cr_nat :: nat \<Rightarrow> nat \<Rightarrow> bool) mn (Rep_nat mn)"
  assumes [transfer_rule]: "(cr_nat :: nat \<Rightarrow> nat \<Rightarrow> bool) nn (Rep_nat nn)"
  shows "cr_nat ?t (plus (Rep_nat mn) (Rep_nat nn))"
  apply (subst plus_case_def)
  apply transfer_prover_start
        apply transfer_step+
  apply (rule HOL.refl)
  done

lemma plus_nat_synth_def:
  fixes m :: nat and n :: nat
  assumes "mn = Abs_nat m"
  assumes "nn = Abs_nat n"
  shows "plus_nat mn nn
    = case_nat_nat mn (\<lambda>x2ba. Suc_nat (plus_nat mn x2ba)) nn"
  apply(rule HOL.trans[OF _ plus_nat_synth[unfolded cr_nat_def, symmetric]])
  using assms cr_nat_nat_equiv
    apply(simp add: plus_nat_def rel_fun_def cr_nat_def)+
  done
thm plus_nat_synth_def[unfolded case_nat_nat_def]

end
