\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_To_IMP_Minus_Datatypes
  imports
    HOL_To_IMP_Minus_Arithmetics
    "HOL-Data_Structures.Cmp"
begin

datatype_compile_nat cmp_val

locale HOL_To_HOL_Nat =
  notes transport_eq_id.partial_equivalence_rel_equivalenceI[per_intro del]
  and transport_eq_restrict_id.partial_equivalence_rel_equivalence[per_intro del]
begin

section \<open>Pairs\<close>

function_compile_nat fst_def
function_compile_nat snd_def

section\<open>Three-way compare\<close>

(* function_compile_nat cmp_def *)

section\<open>Lists\<close>

paragraph \<open>length\<close>

(*
fun length_aux :: "nat \<Rightarrow> 'a list \<Rightarrow> nat" where
  "length_aux acc [] = acc" |
  "length_aux acc (_ # xs) = length_aux (Suc acc) xs"


fun length :: "'a list \<Rightarrow> nat" where
  "length [] = 0" |
  "length (_ # xs) = Suc (length xs)"

lemma "List.length xs = local.length xs" by (induction xs) auto

case_of_simps length_eq : length.simps
function_compile_nat length_eq
*)

lemma length_eq: "length xs = (case xs of [] \<Rightarrow> 0 | (_ # xs') \<Rightarrow> Suc (length xs'))"
  by (simp add: list.case_eq_if)

function_compile_nat length_eq
print_theorems

paragraph\<open>compare_lengths\<close>

fun compare_lengths :: "'a list \<Rightarrow> 'b list \<Rightarrow> cmp_val" where
  "compare_lengths [] [] = EQ" |
  "compare_lengths [] _ = LT" |
  "compare_lengths _ [] = GT" |
  "compare_lengths (_ # xs) (_ # ys) = compare_lengths xs ys"

case_of_simps compare_lengths_eq : compare_lengths.simps

function_compile_nat compare_lengths_eq

paragraph \<open>rev\<close>

fun rev_aux :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rev_aux acc [] = acc" |
  "rev_aux acc (x # xs) = rev_aux (x # acc) xs"

case_of_simps rev_aux_eq : rev_aux.simps

function_compile_nat rev_aux_eq

definition rev :: "'a list \<Rightarrow> 'a list" where
  "rev = rev_aux []"

function_compile_nat rev_def

paragraph \<open>zip\<close>

thm zip.simps
case_of_simps zip_eq : zip.simps
function_compile_nat zip_eq

end

context HOL_To_IMP_Minus
begin

section \<open>Pairs\<close>

compile_nat Pair_nat_def
HOL_To_IMP_Minus_correct Pair_nat by cook

lemmas fst_nat_eq_unfolded = HOL_To_HOL_Nat.fst_nat_eq_unfolded[simplified case_prod_nat_def]
unconditional_nat fst_nat_eq_unfolded
compile_nat fst_nat_unconditional.simps
HOL_To_IMP_Minus_correct fst_nat_unconditional by cook

lemmas snd_nat_eq_unfolded = HOL_To_HOL_Nat.snd_nat_eq_unfolded[simplified case_prod_nat_def]
unconditional_nat snd_nat_eq_unfolded
compile_nat snd_nat_unconditional.simps
HOL_To_IMP_Minus_correct snd_nat_unconditional by cook

section \<open>Three-way compare\<close>

compile_nat LT_nat_def
HOL_To_IMP_Minus_correct LT_nat by cook

compile_nat EQ_nat_def
HOL_To_IMP_Minus_correct EQ_nat by cook

compile_nat GT_nat_def
HOL_To_IMP_Minus_correct GT_nat by cook

section\<open>Lists\<close>

compile_nat Cons_nat_def
HOL_To_IMP_Minus_correct Cons_nat by cook

compile_nat Nil_nat_def
HOL_To_IMP_Minus_correct Nil_nat by cook

paragraph \<open>length\<close>

(* TODO: these all end up getting named size_... *)
thm HOL_To_HOL_Nat.size_nat_eq_unfolded
lemmas size_nat_eq = HOL_To_HOL_Nat.size_nat_eq_unfolded[simplified case_list_nat_def]
unconditional_nat size_nat_eq
compile_nat size_nat_unconditional.simps
(* TODO: also the proof doesn't work *)
(* HOL_To_IMP_Minus_correct size_nat_unconditional by (cook mode = tailcall) *)

paragraph\<open>compare_lengths\<close>

lemmas compare_lengths_nat_eq = HOL_To_HOL_Nat.compare_lengths_nat_eq_unfolded[simplified case_list_nat_def]
unconditional_nat compare_lengths_nat_eq
declare compare_lengths_nat_unconditional.simps [simp del]
compile_nat compare_lengths_nat_unconditional.simps
HOL_To_IMP_Minus_correct compare_lengths_nat_unconditional by (cook mode = tailcall)

paragraph \<open>rev\<close>

lemmas rev_aux_nat_eq = HOL_To_HOL_Nat.rev_aux_nat_eq_unfolded[simplified case_list_nat_def]
unconditional_nat rev_aux_nat_eq
declare rev_aux_nat_unconditional.simps [simp del]
compile_nat rev_aux_nat_unconditional.simps
HOL_To_IMP_Minus_correct rev_aux_nat_unconditional by (cook mode = tailcall)

(*
TODO: can't do functions with helpers!
thm HOL_To_HOL_Nat.rev_nat_eq_unfolded
lemmas rev_nat_eq = HOL_To_HOL_Nat.rev_nat_eq_unfolded[simplified case_list_nat_def]
unconditional_nat rev_nat_eq
*)

paragraph \<open>zip\<close>

lemmas zip_nat_eq = HOL_To_HOL_Nat.zip_nat_eq_unfolded[simplified case_list_nat_def]
unconditional_nat zip_nat_eq
declare zip_nat_unconditional.simps [simp del]
compile_nat zip_nat_unconditional.simps
(* TODO: proof fails *)
(* HOL_To_IMP_Minus_correct zip_nat_unconditional by (cook mode = tailcall) *)

end

end
