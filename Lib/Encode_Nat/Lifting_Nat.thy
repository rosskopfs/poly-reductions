theory Lifting_Nat
  imports
    Main
    "HOL-Library.Nat_Bijection"
    "HOL-Library.Simps_Case_Conv"
    Encode_Nat
begin

unbundle lifting_syntax


(* TODO: still necessary? *)
lemma Domainp_nat_bool_rel[transfer_domain_rule]:
  "Domainp (Rel_nat :: _ \<Rightarrow> bool \<Rightarrow> _) = (\<lambda>x. x = False_nat \<or> x = True_nat)"
  unfolding Rel_nat_def natify_bool.simps
  by (auto split:bool.split)

(* TODO: still necessary? *)
lemma nat_bool_rel_conj[transfer_rule]:
  "(Rel_nat ===> Rel_nat ===> Rel_nat) max (\<and>)"
  unfolding Rel_nat_def natify_bool.simps
  by (simp add: pair_def True_nat_def prod_encode_0 rel_fun_def split: bool.split)

(* TODO: still necessary? *)
lemma nat_bool_rel_disj[transfer_rule]:
  "(Rel_nat ===> Rel_nat ===> Rel_nat) min (\<or>)"
  unfolding Rel_nat_def natify_bool.simps
  by (simp add: pair_def True_nat_def prod_encode_0 rel_fun_def split: bool.split)

(* Example? *)
schematic_goal
  shows "Rel_nat ?t (a \<and> (b \<or> c))"
  by transfer_prover



(* compile_nat *)





fun elemof :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "elemof _ [] = False"
| "elemof y (x#xs) = (if (y = x) then True else elemof y xs)"


function_compile_nat elemof

(*
lemma elemof_related_self [trp_in_dom]:
  "(compile_nat_type_def.R \<Rrightarrow> compile_nat_type_def.R \<Rrightarrow> compile_nat_type_def.R) elemof elemof"
  unfolding Fun_Rel_rel_def
  by auto

trp_term elemof_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where x = "elemof :: ('a :: compile_nat) \<Rightarrow> _"
  by trp_prover

lemma elemof_nat_lifting[transfer_rule]:
  shows "(Rel_nat ===> Rel_nat ===> Rel_nat) (elemof_nat TYPE('a::compile_nat)) (elemof :: 'a \<Rightarrow> _)"
  unfolding rel_fun_eq_Fun_Rel_rel
  by (fact elemof_nat_related'[unfolded rel_inv_Fun_Rel_rel_eq[symmetric] rel_inv_iff_rel])

schematic_goal elemof_nat_synth:
  assumes [transfer_rule]: "(Rel_nat :: nat \<Rightarrow> 'a \<Rightarrow> bool) xn (denatify xn)"
  assumes [transfer_rule]: "(Rel_nat :: nat \<Rightarrow> 'a list \<Rightarrow> bool) xsn (denatify xsn)"
  shows "Rel_nat ?t ((elemof :: 'a::compile_nat \<Rightarrow> _) (denatify xn) (denatify xsn))"
  apply (subst elemof_case_def)
  by transfer_prover
 *)

(* lemma elemof_nat_synth_def:
  fixes x :: "'a::compile_nat " and xs :: "'a list"
  assumes "xn = natify_x"
  assumes "xsn = natify_xs"
  shows "elemof_nat TYPE('a) xn xsn
    = case_list_nat False_nat (\<lambda>y ys. if xn = y then True_nat else elemof_nat TYPE('a) xn ys) xsn"
  apply(rule HOL.trans[OF _ elemof_nat_synth[unfolded Rel_nat_def, symmetric]])
    apply(simp add: elemof_nat_app_eq assms; subst denatify_natify_id)+
  done *)

thm elemof_nat_synth_def[unfolded case_list_nat_def]

fun takeWhile :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "takeWhile P [] = []" |
  "takeWhile P (x # xs) = (if P x then x # takeWhile P xs else [])"

(* TODO: goals for higher-order set up the wrong way*)
(* Note Kevin: do you really want "Rel_nat ni (denatify ni)" as assumptions?
  Why not the more general theorem with assumptions "Rel_nat ni xi" ? *)
function_compile_nat takeWhile
print_theorems
thm takeWhile_nat_synth_def[no_vars]



case_of_simps takeWhile_case_def: takeWhile.simps

unbundle no_comp_syntax

lemma takeWhile_related_self [trp_in_dom]:
  "((compile_nat_type_def.R \<Rrightarrow> compile_nat_type_def.R) \<Rrightarrow> compile_nat_type_def.R \<Rrightarrow> compile_nat_type_def.R)
  takeWhile takeWhile"
  by auto

trp_term takeWhile_nat :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat"
  where x = "takeWhile :: (('a :: compile_nat) \<Rightarrow> bool) \<Rightarrow> _"
  by trp_prover

lemma takeWhile_nat_lifting[transfer_rule]:
  "((Rel_nat ===> Rel_nat) ===> Rel_nat ===> Rel_nat)
  (takeWhile_nat TYPE('a::compile_nat)) ((takeWhile :: ('a \<Rightarrow> bool) \<Rightarrow> _))"
  using takeWhile_nat_related'
  by(simp add:  rel_fun_eq_Fun_Rel_rel flip: rel_inv_Fun_Rel_rel_eq)

term "(Rel_nat ===> Rel_nat ===> Rel_nat) P_nat P"
term "(Rel_nat ===> (Rel_nat ===> Rel_nat)) P_nat P"
term "(Rel_nat ===> (Rel_nat ===> Rel_nat) ===> Rel_nat) P_nat P"


schematic_goal takeWhile_nat_synth:
  fixes x1 :: "'a::compile_nat \<Rightarrow> bool" and x2 :: "'a list"
  assumes [transfer_rule]: "Rel_nat n2 x2"
  assumes [transfer_rule]: "(Rel_nat ===> Rel_nat) n1 x1"
  shows "Rel_nat ?t (takeWhile x1 x2)"
  by (subst takeWhile_case_def) transfer_prover

term "(pred_map natify (pred_map n1 denatify))"
thm HOL.trans[OF _ takeWhile_nat_synth[unfolded Rel_nat_def, symmetric]]

lemma "\<lbrakk>\<forall>y. n1 (natify y) = natify (x1 y); n2 = natify x2\<rbrakk> \<Longrightarrow>
  takeWhile_nat TYPE('a::compile_nat) n1 (natify x2) = natify (takeWhile x1 x2)"
  oops

lemma takeWhile_nat_synth_def:
  fixes x1 :: "'a::compile_nat \<Rightarrow> bool" and x2 :: "'a list"
  assumes "(Rel_nat ===> Rel_nat) n1 x1"
  assumes "Rel_nat n2 x2"
  shows "takeWhile_nat TYPE('a) n1 n2
    = case_list_nat Nil_nat
        (\<lambda>a b. If_nat TYPE('a list) (n1 a) (Cons_nat a (takeWhile_nat TYPE('a) n1 b)) Nil_nat) n2"
  apply (tactic \<open>Classical.rule_tac @{context}
      @{thms HOL.trans[OF _ takeWhile_nat_synth[unfolded Rel_nat_def, symmetric]]} [] 1\<close>)
    defer prefer 2 prefer 3
  thm assms
    apply(tactic \<open>ALLGOALS (Method.insert_tac @{context} @{thms assms})\<close>)
    apply(tactic \<open>auto_tac (@{context} addsimps @{thms takeWhile_nat_app_eq rel_fun_def Rel_nat_def})\<close>)
apply (auto simp add: takeWhile_nat_app_eq Rel_nat_def rel_fun_def)

  thm takeWhile_nat_synth[unfolded Rel_nat_def, symmetric, of n2 "denatify n2" n1 ]
  thm HOL.trans[OF _ takeWhile_nat_synth[unfolded Rel_nat_def, symmetric, of n2 x2 n1 x1]]
      HOL.trans[OF _ takeWhile_nat_synth[unfolded Rel_nat_def, symmetric]]
  apply(rule HOL.trans[OF _ takeWhile_nat_synth[unfolded Rel_nat_def, symmetric]])
  using assms apply (auto simp add: takeWhile_nat_app_eq Rel_nat_def rel_fun_def)
    apply (simp add: takeWhile_nat_app_eq[of n1 n2, where ?'a='a])
  using assms apply(simp add: assms Rel_nat_def)
  using assms unfolding Rel_nat_def rel_fun_def apply simp
  using assms
    apply(si mp add: assms takeWhile_nat_app_eq rel_fun_def Rel_nat_def)+
  done

thm takeWhile_nat_synth_def[unfolded case_list_nat_def]

fun head :: "'a list \<Rightarrow> 'a" where
  "head [] = undefined" |
  "head (x # _) = x"

function_compile_nat head
  (*
case_of_simps head_case_def: head.simps

definition head_nat :: "'a::compile_nat itself \<Rightarrow> nat \<Rightarrow> nat" where
  "head_nat _ xsn \<equiv> (natify_:: 'a \<Rightarrow> nat) (head (denatify xsn))"

lemma head_nat_lifting[transfer_rule]:
  shows "(Rel_nat ===> Rel_nat) (head_nat TYPE('a::compile_nat)) (head :: 'a list \<Rightarrow> _)"
  unfolding head_nat_def Rel_nat_def
  by(simp add: rel_fun_def)

schematic_goal head_nat_synth:
  assumes [transfer_rule]: "(Rel_nat :: nat \<Rightarrow> 'a list \<Rightarrow> bool) xsn (denatify xsn)"
  shows "Rel_nat ?t ((head :: 'a::compile_nat list \<Rightarrow> _) (denatify xsn))"
  apply (subst head_case_def)
  by transfer_prover *)

(* lemma head_nat_synth_def:
  fixes xs :: "'a::compile_nat list"
  assumes "xsn = natify_xs"
  shows "head_nat TYPE('a) xsn
    = case_list_nat (natify_(undefined::'a)) (\<lambda>x2a x1a. x2a) xsn"
  apply(rule HOL.trans[OF _ head_nat_synth[unfolded Rel_nat_def, symmetric]])
   apply(simp add: head_nat_app_eq assms; subst denatify_natify_id)+
  done *)

thm head_nat_synth_def[unfolded case_list_nat_def]

fun append :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "append xs [] = xs" |
  "append xs ys = rev_tr ys (rev_tr [] xs)"

function_compile_nat append

(* case_of_simps append_case_def: append.simps

definition append_nat :: "'a::compile_nat itself \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "append_nat _ xsn ysn \<equiv> (natify_:: 'a list \<Rightarrow> nat) (append (denatify xsn) (denatify ysn))"

lemma append_nat_lifting[transfer_rule]:
  shows "(Rel_nat ===> Rel_nat ===> Rel_nat) (append_nat TYPE('a::compile_nat))
  (append :: 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list)"
  by(simp add: append_nat_def rel_fun_def Fun.comp_def Rel_nat_def)

schematic_goal append_nat_synth:
  assumes [transfer_rule]: "(Rel_nat :: nat \<Rightarrow> 'a list \<Rightarrow> bool) xsn (denatify xsn)"
  assumes [transfer_rule]: "(Rel_nat :: nat \<Rightarrow> 'a list \<Rightarrow> bool) ysn (denatify ysn)"
  shows "Rel_nat ?t ((append :: 'a::compile_nat list \<Rightarrow> _) (denatify xsn) (denatify ysn))"
  apply (subst append_case_def)
  by transfer_prover *)

(* lemma append_nat_synth_def:
  fixes xs :: "'a::compile_nat list" and ys :: "'a list"
  assumes "xsn = natify_xs"
  assumes "ysn = natify_ys"
  shows "append_nat TYPE('a) xsn ysn = case_list_nat xsn (\<lambda>x3a x2ba. rev_tr_nat TYPE('a)
                (Cons_nat x3a x2ba) (rev_tr_nat TYPE('a) Nil_nat xsn)) ysn"
  apply(rule HOL.trans[OF _ append_nat_synth[unfolded Rel_nat_def, symmetric]])
    apply(simp add: append_nat_app_eq assms; subst denatify_natify_id)+
  done
 *)


fun plus :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "plus m 0 = m" |
  "plus m (Suc n) = Suc (plus m n)"


(* TODO: Not working yet. Explicitly specify L in trp_term *)
function_compile_nat plus

case_of_simps plus_case_def: plus.simps

lemma plus_related_self [trp_in_dom]:
  "(compile_nat_type_def.R \<Rrightarrow> compile_nat_type_def.R \<Rrightarrow> compile_nat_type_def.R) plus plus"
  unfolding Fun_Rel_rel_def
  by auto

trp_term plus_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where x = "plus :: nat \<Rightarrow> nat \<Rightarrow> nat"
  and L = "(compile_nat_type_def.R \<Rrightarrow> compile_nat_type_def.R \<Rrightarrow> compile_nat_type_def.R)"
  by trp_prover


thm plus_nat_related' rev_tr_nat_related'
term "(Rel_nat :: nat \<Rightarrow> nat \<Rightarrow> bool)\<inverse> \<Rrightarrow> (Rel_nat :: nat \<Rightarrow> nat \<Rightarrow> bool)\<inverse> \<Rrightarrow> (Rel_nat :: nat \<Rightarrow> nat \<Rightarrow> bool)\<inverse>"

lemma plus_nat_lifting[transfer_rule]:
  shows "(Rel_nat ===> Rel_nat ===> Rel_nat) plus_nat plus"
  using plus_nat_related'
  by(simp add:  rel_fun_eq_Fun_Rel_rel flip: rel_inv_Fun_Rel_rel_eq)


schematic_goal plus_nat_synth:
  assumes [transfer_rule]: "(Rel_nat :: nat \<Rightarrow> nat \<Rightarrow> bool) mn m"
  assumes [transfer_rule]: "(Rel_nat :: nat \<Rightarrow> nat \<Rightarrow> bool) nn n"
  shows "Rel_nat ?t (plus m n)"
  apply (subst plus_case_def)
  by transfer_prover

lemma plus_nat_synth_def:
  fixes m :: nat and n :: nat
  assumes "Rel_nat mn n"
  assumes "Rel_nat nn n"
  shows "plus_nat mn nn
    = case_nat_nat mn (\<lambda>x2ba. Suc_nat (plus_nat mn x2ba)) nn"
  apply(rule HOL.trans[OF _ plus_nat_synth[unfolded Rel_nat_def, symmetric]])
  using assms by (simp add: plus_nat_app_eq Rel_nat_def)+

thm plus_nat_synth_def[unfolded case_nat_nat_def]

end
