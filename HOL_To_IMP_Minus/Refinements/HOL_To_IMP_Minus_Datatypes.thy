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


section \<open>Pair\<close>

function_compile_nat fst_def
function_compile_nat snd_def


section\<open>Three-way compare\<close>

(* would require ord typeclass *)
(* function_compile_nat cmp_def *)


section\<open>Comparison (nat)\<close>

fun "leq_aux" :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "leq_aux 0 _ = True" |
  "leq_aux (Suc _) 0 = False" |
  "leq_aux (Suc x) (Suc y) = leq_aux x y"

lemma leq_eq_leq_aux: "(x \<le> y) \<equiv> leq_aux x y"
  by (induction x y rule: leq_aux.induct) auto

case_of_simps leq_aux_eq : leq_aux.simps
function_compile_nat leq_aux_eq
function_compile_nat leq_eq_leq_aux


section \<open>Option\<close>

paragraph \<open>is_some\<close>

fun is_some :: "'a option \<Rightarrow> bool" where
  "is_some (Some _) = True" |
  "is_some None = False"

case_of_simps is_some_eq : is_some.simps
function_compile_nat is_some_eq


paragraph \<open>get_some\<close>

fun get_some :: "'a \<Rightarrow> 'a option \<Rightarrow> 'a" where
  "get_some _ (Some x) = x" |
  "get_some d _ = d"

case_of_simps get_some_eq : get_some.simps
function_compile_nat get_some_eq


section\<open>List\<close>

paragraph \<open>length\<close>

fun length_aux :: "nat \<Rightarrow> 'a list \<Rightarrow> nat" where
  "length_aux acc [] = acc" |
  "length_aux acc (_ # xs) = length_aux (Suc acc) xs"

lemma length_eq_length_aux: "List.length xs + k = length_aux k xs"
  by (induction k xs rule: length_aux.induct) auto

lemma length_eq_length_aux0: "List.length xs = length_aux 0 xs"
  by (rule length_eq_length_aux[where k = 0, simplified])

case_of_simps length_aux_eq : length_aux.simps
function_compile_nat length_aux_eq
function_compile_nat length_eq_length_aux0


paragraph\<open>compare_lengths\<close>

fun compare_lengths :: "'a list \<Rightarrow> 'b list \<Rightarrow> cmp_val" where
  "compare_lengths [] [] = EQ" |
  "compare_lengths [] _ = LT" |
  "compare_lengths _ [] = GT" |
  "compare_lengths (_ # xs) (_ # ys) = compare_lengths xs ys"

case_of_simps compare_lengths_eq : compare_lengths.simps
function_compile_nat compare_lengths_eq


paragraph \<open>rev_aux\<close>

fun rev_aux :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rev_aux acc [] = acc" |
  "rev_aux acc (x # xs) = rev_aux (x # acc) xs"

case_of_simps rev_aux_eq : rev_aux.simps
function_compile_nat rev_aux_eq


paragraph \<open>rev\<close>

lemma rev_eq_rev_aux: "List.rev xs @ ys = local.rev_aux ys xs"
  by (induction ys xs rule: rev_aux.induct) auto

lemma rev_eq_rev_aux0: "List.rev = rev_aux []"
  using rev_eq_rev_aux[where ys = "[]"] by auto

function_compile_nat rev_eq_rev_aux0


paragraph \<open>append\<close>

lemma append_eq_rev_aux: "List.append xs ys = rev_aux ys (rev xs)"
  unfolding rev_eq_rev_aux[symmetric] by simp

function_compile_nat append_eq_rev_aux


paragraph \<open>zip\<close>

fun zip_aux :: "('a \<times> 'b) list \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) list" where
  "zip_aux acc [] _ = acc" |
  "zip_aux acc _ [] = acc" |
  "zip_aux acc (x # xs) (y # ys) = zip_aux ((x, y) # acc) xs ys"

lemma zip_eq_zip_aux: "rev zs @ List.zip xs ys = rev (zip_aux zs xs ys)"
  apply (induction zs xs ys rule: zip_aux.induct)
  unfolding rev_eq_rev_aux[symmetric] by auto

lemma zip_eq_zip_aux0: "List.zip xs ys = rev (zip_aux [] xs ys)"
  using zip_eq_zip_aux[where zs = "[]"]
  unfolding rev_eq_rev_aux[symmetric] by auto

case_of_simps zip_aux_eq : zip_aux.simps
function_compile_nat zip_aux_eq
function_compile_nat zip_eq_zip_aux0 (* TODO: this step is quite a bit slower *)


subsection \<open>Association Lists\<close>

fun assoc_lookup :: "'k \<Rightarrow> ('k \<times> 'v) list \<Rightarrow> 'v option" where
  "assoc_lookup _ [] = None" |
  "assoc_lookup x ((k, v) # xs) = (if x = k then Some v else assoc_lookup k xs)"

case_of_simps assoc_lookup_eq : assoc_lookup.simps
function_compile_nat assoc_lookup_eq

end

context HOL_To_IMP_Minus
begin

section \<open>Bool\<close>

compile_nat True_nat_def
HOL_To_IMP_Minus_correct True_nat by cook

compile_nat False_nat_def
HOL_To_IMP_Minus_correct False_nat by cook


section \<open>Pair\<close>

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


section\<open>Comparison (nat)\<close>

lemmas leq_aux_nat_eq = HOL_To_HOL_Nat.leq_aux_nat_eq_unfolded[simplified case_nat_eq_if]
unconditional_nat leq_aux_nat_eq
declare leq_aux_nat_unconditional.simps [simp del]
compile_nat leq_aux_nat_unconditional.simps
HOL_To_IMP_Minus_correct leq_aux_nat_unconditional by (cook mode = tailcall)

unconditional_nat HOL_To_HOL_Nat.leq_eq_leq_aux
declare less_eq_unconditional.simps [simp del]
(* compile_nat less_eq_unconditional.simps *)
(* HOL_To_IMP_Minus_correct less_eq_unconditional by cook *)


section \<open>Option\<close>

compile_nat None_nat_def
HOL_To_IMP_Minus_correct None_nat by cook

compile_nat Some_nat_def
HOL_To_IMP_Minus_correct Some_nat by cook


paragraph \<open>is_some\<close>

lemmas is_some_nat_eq = HOL_To_HOL_Nat.is_some_nat_eq_unfolded[simplified case_option_nat_def]
unconditional_nat is_some_nat_eq
declare is_some_nat_unconditional.simps [simp del]
compile_nat is_some_nat_unconditional.simps
HOL_To_IMP_Minus_correct is_some_nat_unconditional by cook

paragraph \<open>get_some\<close>

lemmas get_some_nat_eq = HOL_To_HOL_Nat.get_some_nat_eq_unfolded[simplified case_option_nat_def]
unconditional_nat get_some_nat_eq
declare get_some_nat_unconditional.simps [simp del]
compile_nat get_some_nat_unconditional.simps
HOL_To_IMP_Minus_correct get_some_nat_unconditional by cook


section\<open>Lists\<close>

compile_nat Cons_nat_def
HOL_To_IMP_Minus_correct Cons_nat by cook

compile_nat Nil_nat_def
HOL_To_IMP_Minus_correct Nil_nat by cook

paragraph \<open>length\<close>

lemmas length_aux_nat_eq = HOL_To_HOL_Nat.length_aux_nat_eq_unfolded[simplified case_list_nat_def]
unconditional_nat length_aux_nat_eq
declare length_aux_nat_unconditional.simps [simp del]
compile_nat length_aux_nat_unconditional.simps
HOL_To_IMP_Minus_correct length_aux_nat_unconditional by (cook mode = tailcall)

(* TODO: this ends up getting named size_* *)
lemmas length_nat_eq = HOL_To_HOL_Nat.size_nat_eq_unfolded[simplified case_list_nat_def]
(* unconditional_nat length_nat_eq *)
(* declare length_nat_unconditional.simps [simp del] *)
(* compile_nat length_nat_unconditional.simps *)
(* HOL_To_IMP_Minus_correct length_nat_unconditional by cook *)


paragraph\<open>compare_lengths\<close>

lemmas compare_lengths_nat_eq = HOL_To_HOL_Nat.compare_lengths_nat_eq_unfolded[simplified case_list_nat_def]
unconditional_nat compare_lengths_nat_eq
declare compare_lengths_nat_unconditional.simps [simp del]
compile_nat compare_lengths_nat_unconditional.simps
HOL_To_IMP_Minus_correct compare_lengths_nat_unconditional by (cook mode = tailcall)


paragraph \<open>rev_aux\<close>

lemmas rev_aux_nat_eq = HOL_To_HOL_Nat.rev_aux_nat_eq_unfolded[simplified case_list_nat_def]
unconditional_nat rev_aux_nat_eq
declare rev_aux_nat_unconditional.simps [simp del]
compile_nat rev_aux_nat_unconditional.simps
HOL_To_IMP_Minus_correct rev_aux_nat_unconditional by (cook mode = tailcall)

paragraph \<open>rev\<close>

(* TODO: aux function rev_aux needed for rev *)


paragraph \<open>append\<close>

(* TODO: aux function rev_aux needed for append *)


paragraph \<open>zip\<close>

lemmas zip_aux_nat_eq = HOL_To_HOL_Nat.zip_aux_nat_eq_unfolded[simplified case_list_nat_def]
unconditional_nat zip_aux_nat_eq
declare zip_aux_nat_unconditional.simps [simp del]
compile_nat zip_aux_nat_unconditional.simps
HOL_To_IMP_Minus_correct zip_aux_nat_unconditional by (cook mode = tailcall)

(* TODO: aux function rev needed for zip *)


subsection \<open>Association Lists\<close>

lemmas assoc_lookup_nat_eq = HOL_To_HOL_Nat.assoc_lookup_nat_eq_unfolded[simplified case_list_nat_def case_prod_nat_def]
unconditional_nat assoc_lookup_nat_eq
declare assoc_lookup_nat_unconditional.simps [simp del]
compile_nat assoc_lookup_nat_unconditional.simps
HOL_To_IMP_Minus_correct assoc_lookup_nat_unconditional by (cook mode = tailcall)

end

end
