\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_To_IMP_Minus_Datatypes
  imports
    HOL_To_IMP_Minus_Arithmetics
    "HOL-Data_Structures.Cmp"
begin

datatype_compile_nat cmp_val
datatype 'a my_option = None | Some 'a
datatype_compile_nat my_option
(* datatype_compile_nat option *) (* ?? *)

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

fun is_some :: "'a my_option \<Rightarrow> bool" where
  "is_some (Some _) = True" |
  "is_some None = False"

case_of_simps is_some_eq : is_some.simps
function_compile_nat is_some_eq


paragraph \<open>get_some\<close>

fun get_some :: "'a \<Rightarrow> 'a my_option \<Rightarrow> 'a" where
  "get_some _ (Some x) = x" |
  "get_some d _ = d"

case_of_simps get_some_eq : get_some.simps
function_compile_nat get_some_eq


section\<open>List\<close>

paragraph \<open>length\<close>

fun length_aux :: "nat \<Rightarrow> 'a list \<Rightarrow> nat" where
  "length_aux acc [] = acc" |
  "length_aux acc (_ # xs) = length_aux (Suc acc) xs"

(* definition length0 :: "'a list \<Rightarrow> nat" where *)
  (* "length0 = length_aux 0" *)

lemma length_eq_length_aux: "List.length xs + k = length_aux k xs"
  by (induction k xs rule: length_aux.induct) auto

lemma length_eq_length0: "List.length xs = length_aux 0 xs"
  (* unfolding length0_def *)
  by (rule length_eq_length_aux[where k = 0, simplified])

case_of_simps length_aux_eq : length_aux.simps
function_compile_nat length_aux_eq
(* function_compile_nat length0_def *)
function_compile_nat length_eq_length0


paragraph\<open>compare_lengths\<close>

fun compare_lengths :: "'a list \<Rightarrow> 'b list \<Rightarrow> cmp_val" where
  "compare_lengths [] [] = EQ" |
  "compare_lengths [] _ = LT" |
  "compare_lengths _ [] = GT" |
  "compare_lengths (_ # xs) (_ # ys) = compare_lengths xs ys"

case_of_simps compare_lengths_eq : compare_lengths.simps
function_compile_nat compare_lengths_eq


paragraph \<open>rev_append\<close>

fun rev_append :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rev_append [] acc = acc" |
  "rev_append (x # xs) acc = rev_append xs (x # acc)"

case_of_simps rev_append_eq : rev_append.simps
function_compile_nat rev_append_eq


paragraph \<open>rev\<close>

definition rev0 :: "'a list \<Rightarrow> 'a list" where
  "rev0 xs = rev_append xs []"

lemma rev_eq_rev_aux: "List.rev xs @ ys = local.rev_append xs ys"
  by (induction xs ys rule: rev_append.induct) auto

lemma rev_eq_rev0: "List.rev xs = local.rev0 xs"
  unfolding rev0_def
  using rev_eq_rev_aux[where ys = "[]"] by simp

function_compile_nat rev0_def
function_compile_nat rev_eq_rev0


paragraph \<open>append\<close>

lemma append_eq_append0: "List.append xs ys = rev_append (rev xs) ys"
  unfolding rev_eq_rev_aux[symmetric] by simp

function_compile_nat append_eq_append0


paragraph \<open>zip\<close>

fun zip_aux :: "('a \<times> 'b) list \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) list" where
  "zip_aux acc [] _ = acc" |
  "zip_aux acc _ [] = acc" |
  "zip_aux acc (x # xs) (y # ys) = zip_aux ((x, y) # acc) xs ys"

lemma zip_eq_zip_aux: "rev zs @ List.zip xs ys = rev (zip_aux zs xs ys)"
  apply (induction zs xs ys rule: zip_aux.induct)
  unfolding rev_eq_rev0[symmetric] by auto

lemma zip_eq_zip_aux0: "List.zip xs ys = rev (zip_aux [] xs ys)"
  using zip_eq_zip_aux[where zs = "[]"]
  unfolding rev_eq_rev0[symmetric] by auto

case_of_simps zip_aux_eq : zip_aux.simps
function_compile_nat zip_aux_eq
function_compile_nat zip_eq_zip_aux0 (* slow? *)


subsection \<open>Association Lists\<close>

fun assoc_lookup :: "'k \<Rightarrow> ('k \<times> 'v) list \<Rightarrow> 'v my_option" where
  "assoc_lookup _ [] = None" |
  "assoc_lookup x ((k, v) # xs) = (if x = k then Some v else assoc_lookup k xs)"

case_of_simps assoc_lookup_eq : assoc_lookup.simps
function_compile_nat assoc_lookup_eq

(* TODO: assoc_delete, assoc_update *)

subsection \<open>Sorting\<close>

text \<open>Sorting, based on decorate-sort-undecorate. Sorts tuples (nat, 'a) on the nat component.
  For sorting arbitrary datatypes, they must first be mapped to an integer key, sorted, then
  the key stripped away. Best we can do, since we cannot write a polymorphic sort.\<close>
(* TODO: or can we do something with typeclasses? *)

type_synonym 'a sort_key = "(nat \<times> 'a)"

fun insort_deco_aux :: "'a sort_key list \<Rightarrow> 'a sort_key \<Rightarrow> 'a sort_key list \<Rightarrow> 'a sort_key list" where
  "insort_deco_aux acc k [] = rev (k # acc)" |
  "insort_deco_aux acc k' (k # xs) =
    (if fst k' \<le> fst k then rev_append (k' # acc) (k # xs) else insort_deco_aux (k # acc) k' xs)"

case_of_simps insort_deco_aux_eq : insort_deco_aux.simps
(* function_compile_nat insort_deco_aux_eq *)
(* this refuses to compile *)

lemma insort_key_fst_eq_insort_deco_aux: "rev acc @ insort_key fst k xs = insort_deco_aux acc k xs"
  apply (induction acc k xs rule: insort_deco_aux.induct) using rev_eq_rev_aux by auto

definition insort_deco :: "'a sort_key \<Rightarrow> 'a sort_key list \<Rightarrow> 'a sort_key list" where
  "insort_deco = insort_deco_aux []"

lemma insort_key_fst_eq_insort_deco_aux0: "insort_key fst k xs = insort_deco k xs"
  unfolding insort_deco_def using insort_key_fst_eq_insort_deco_aux[where acc = "[]", simplified] by fast

(* function_compile_nat insort_deco_def *)

fun sort_deco_aux :: "'a sort_key list \<Rightarrow> 'a sort_key list \<Rightarrow> 'a sort_key list" where
  "sort_deco_aux acc [] = acc" |
  "sort_deco_aux acc (x # xs) = sort_deco_aux (insort_deco x acc) xs"

case_of_simps sort_deco_aux_eq : sort_deco_aux.simps
(* function_compile_nat sort_deco_aux_eq *)

lemma sort_key_eq_sort_deco_aux:
  assumes sorted_acc: "sorted (map fst acc)" shows "sort_key fst (xs @ acc) = sort_deco_aux acc (rev xs)"
proof-
  have "sort_key fst (xs @ acc) = foldl (\<lambda>x y. insort_key fst y x) acc (rev xs)"
    by (subst sort_key_def, subst foldr_append, subst sort_key_def[symmetric],
        subst sort_key_id_if_sorted[OF sorted_acc], subst foldr_conv_foldl, rule refl)
  moreover have "foldl (\<lambda>x y. insort_key fst y x) acc xs = sort_deco_aux acc xs" for xs
    by (induction xs arbitrary: acc) (auto simp add: insort_key_fst_eq_insort_deco_aux0)
  ultimately show "sort_key fst (xs @ acc) = sort_deco_aux acc (rev xs)" by simp
qed

lemma sort_key_eq_sort_deco_aux0: "sort_key fst xs = sort_deco_aux [] (rev xs)"
  using sort_key_eq_sort_deco_aux[where acc = "[]"] by auto

definition sort_deco :: "'a sort_key list \<Rightarrow> 'a sort_key list" where
  "sort_deco = sort_deco_aux []"

(* function_compile_nat sort_deco_def *)

(* For sort_deco and helpers it's not really clear how to generate a "drop-in" compilable function
   compatible with sort, since we can't compile "sort_key fst" to IMP. Thus, code will
   need to call sort_deco directly (but the correctness lemmas should still be useful). *)

fun undecorate_aux :: "'a list \<Rightarrow> 'a sort_key list \<Rightarrow> 'a list" where
  "undecorate_aux acc [] = rev acc" | "undecorate_aux acc ((_, x) # xs) = undecorate_aux (x # acc) xs"

definition undecorate :: "'a sort_key list \<Rightarrow> 'a list" where
  "undecorate = undecorate_aux []"

case_of_simps undecorate_aux_eq : undecorate_aux.simps
function_compile_nat undecorate_aux_eq
function_compile_nat undecorate_def

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

find_theorems "case (?x :: nat) of (0) \<Rightarrow> _ | (Suc n) \<Rightarrow> _" "if ?x = 0 then _ else _"

lemmas leq_aux_nat_eq = HOL_To_HOL_Nat.leq_aux_nat_eq_unfolded[simplified case_nat_eq_if]
unconditional_nat leq_aux_nat_eq
declare leq_aux_nat_unconditional.simps [simp del]
compile_nat leq_aux_nat_unconditional.simps
HOL_To_IMP_Minus_correct leq_aux_nat_unconditional by (cook mode = tailcall)

unconditional_nat HOL_To_HOL_Nat.leq_eq_leq_aux
declare less_eq_unconditional.simps [simp del]
(* TODO: uses helper function *)
(* compile_nat less_eq_unconditional.simps *)
(* HOL_To_IMP_Minus_correct less_eq_unconditional by cook *)


section \<open>Option\<close>

compile_nat None_nat_def
HOL_To_IMP_Minus_correct None_nat by cook

compile_nat Some_nat_def
HOL_To_IMP_Minus_correct Some_nat by cook


paragraph \<open>is_some\<close>

lemmas is_some_nat_eq = HOL_To_HOL_Nat.is_some_nat_eq_unfolded[simplified case_my_option_nat_def]
unconditional_nat is_some_nat_eq
declare is_some_nat_unconditional.simps [simp del]
compile_nat is_some_nat_unconditional.simps
HOL_To_IMP_Minus_correct is_some_nat_unconditional by cook

paragraph \<open>get_some\<close>

lemmas get_some_nat_eq = HOL_To_HOL_Nat.get_some_nat_eq_unfolded[simplified case_my_option_nat_def]
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

(* TODO: this ends up getting named size_... *)
lemmas length_nat_eq = HOL_To_HOL_Nat.size_nat_eq_unfolded[simplified case_list_nat_def]
(* TODO: uses helper function *)
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


paragraph \<open>rev_append\<close>

lemmas rev_append_nat_eq = HOL_To_HOL_Nat.rev_append_nat_eq_unfolded[simplified case_list_nat_def]
unconditional_nat rev_append_nat_eq
declare rev_append_nat_unconditional.simps [simp del]
compile_nat rev_append_nat_unconditional.simps
HOL_To_IMP_Minus_correct rev_append_nat_unconditional by (cook mode = tailcall)

paragraph \<open>rev\<close>

(* TODO: can't do functions with helpers! *)


paragraph \<open>append\<close>

(* TODO: aux function *)


paragraph \<open>zip\<close>

lemmas zip_aux_nat_eq = HOL_To_HOL_Nat.zip_aux_nat_eq_unfolded[simplified case_list_nat_def]
unconditional_nat zip_aux_nat_eq
declare zip_aux_nat_unconditional.simps [simp del]
compile_nat zip_aux_nat_unconditional.simps
HOL_To_IMP_Minus_correct zip_aux_nat_unconditional by (cook mode = tailcall)

(* TODO: zip: aux function needed *)


subsection \<open>Association Lists\<close>

lemmas assoc_lookup_nat_eq = HOL_To_HOL_Nat.assoc_lookup_nat_eq_unfolded[simplified case_list_nat_def case_prod_nat_def]
unconditional_nat assoc_lookup_nat_eq
declare assoc_lookup_nat_unconditional.simps [simp del]
compile_nat assoc_lookup_nat_unconditional.simps
HOL_To_IMP_Minus_correct assoc_lookup_nat_unconditional by (cook mode = tailcall)


subsection \<open>Sorting\<close>

(* TODO: get compiling to Nat first *)


end

end
