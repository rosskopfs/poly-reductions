\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_To_IMP_Minus_Primitives
  imports
    HOL_Nat_To_IMP_Minus.HOL_Nat_To_IMP_Tactics
begin

paragraph \<open>Equality\<close>

locale HOL_To_HOL_Nat =
  notes transport_eq_id.partial_equivalence_rel_equivalenceI[per_intro del]
  and transport_eq_restrict_id.partial_equivalence_rel_equivalence[per_intro del]
begin

definition "eq_nat (n :: nat) m \<equiv> if (n - m) + (m - n) = 0 then True_nat else False_nat"

lemma eq_nat_eq [HOL_To_IMP_finish_simps]: "eq_nat n m = natify (n = m)"
  unfolding eq_nat_def natify_bool_def by simp

lemma Rel_nat_eq_nat [Rel_nat_related]: "(Rel_nat ===> Rel_nat ===> Rel_nat) eq_nat (=)"
proof (intro rel_funI)
  fix x x' and y y' :: 'a
  assume "Rel_nat x y" "Rel_nat x' y'"
  then show "Rel_nat (eq_nat x x') (y = y')"
  by (cases "y = y'") (simp add: Rel_nat_iff_eq_natify compile_nat_type_def.Rep_inject eq_nat_eq)
qed

end

locale HOL_Nat_To_IMP_Minus =
  notes neq0_conv[iff del, symmetric, iff] Nat.One_nat_def[simp del]
begin

sublocale HTHN : HOL_To_HOL_Nat .

context includes com_syntax and no com'_syntax
begin

definition [compiled_IMP_Minus_const_def]:
  "eq_IMP \<equiv>
    ''eq.x_Sub_y'' ::= (V ''eq.args.x'' \<ominus> V ''eq.args.y'');;
    ''eq.y_Sub_x'' ::= (V ''eq.args.y'' \<ominus> V ''eq.args.x'');;
    ''eq.neq'' ::= (V ''eq.x_Sub_y'' \<oplus> V ''eq.y_Sub_x'');;
    IF ''eq.neq'' \<noteq>0
    THEN ''eq.ret'' ::= A (N False_nat)
    ELSE ''eq.ret'' ::= A (N True_nat)"

end

declare_compiled_const HTHN.eq_nat
  return_register "eq.ret"
  argument_registers "eq.args.x" "eq.args.y"
  compiled eq_IMP

declare_compiled_const HOL.eq
  return_register "eq.ret"
  argument_registers "eq.args.x" "eq.args.y"
  compiled eq_IMP

HOL_To_IMP_Minus_correct HTHN.eq_nat
  unfolding eq_IMP_def HTHN.eq_nat_def
  by (fastforce intro: terminates_with_res_IMP_MinusI terminates_with_IMP_MinusI)

end

paragraph \<open>Addition and Subtraction\<close>

context HOL_To_HOL_Nat
begin

sublocale HNTIM : HOL_Nat_To_IMP_Minus .

lemma Rel_nat_add [Rel_nat_related]:
  "(Rel_nat ===> Rel_nat ===> Rel_nat) (+) ((+) :: nat \<Rightarrow> _)"
  by (auto simp: Rel_nat_nat_eq_eq)

lemma Rel_nat_sub [Rel_nat_related]:
  "(Rel_nat ===> Rel_nat ===> Rel_nat) (-) ((-) :: nat \<Rightarrow> _)"
  by (auto simp: Rel_nat_nat_eq_eq)

end

context HOL_Nat_To_IMP_Minus
begin

context includes com_syntax and no com'_syntax
begin

definition [compiled_IMP_Minus_const_def]:
  "add_IMP \<equiv> ''add.ret'' ::= (V ''add.args.x'' \<oplus> V ''add.args.y'')"
definition [compiled_IMP_Minus_const_def]:
  "sub_IMP \<equiv> ''sub.ret'' ::= (V ''sub.args.x'' \<ominus> V ''sub.args.y'')"

end

declare_compiled_const "Groups.plus"
  return_register "add.ret"
  argument_registers "add.args.x" "add.args.y"
  compiled "add_IMP"

declare_compiled_const "Groups.minus"
  return_register "sub.ret"
  argument_registers "sub.args.x" "sub.args.y"
  compiled "sub_IMP"

HOL_To_IMP_Minus_correct Groups.plus
  unfolding add_IMP_def
  by (fastforce intro: terminates_with_res_IMP_MinusI terminates_with_IMP_MinusI)
HOL_To_IMP_Minus_correct Groups.minus
  unfolding sub_IMP_def
  by (fastforce intro: terminates_with_res_IMP_MinusI terminates_with_IMP_MinusI)

end

paragraph \<open>Multiplication\<close>

context HOL_To_HOL_Nat
begin

fun mul_acc_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"mul_acc_nat 0 _ z = z" |
"mul_acc_nat (Suc x) y z = mul_acc_nat x y (y + z)"
declare mul_acc_nat.simps[simp del]

lemma mul_acc_nat_eq_mul_add: "mul_acc_nat x y z = x * y + z"
  by (induction x y z arbitrary: z rule: mul_acc_nat.induct)
  (auto simp: mul_acc_nat.simps mult_eq_if)

lemma mul_eq_mul_acc_nat_zero: "x * y = mul_acc_nat x y 0"
  using mul_acc_nat_eq_mul_add by simp

lemma Rel_nat_mul [Rel_nat_related]:
  "(Rel_nat ===> Rel_nat ===> Rel_nat) (*) ((*) :: nat \<Rightarrow> _)"
  by (auto simp: Rel_nat_nat_eq_eq)

end

context HOL_Nat_To_IMP_Minus
begin

lemma case_nat_eq_if: "(case n of 0 \<Rightarrow> x | Suc x \<Rightarrow> f x) = (if n = 0 then x else f (n - 1))"
  by (cases n type: nat) auto

case_of_simps mul_acc_nat_eq[simplified case_nat_eq_if] : HTHN.mul_acc_nat.simps
compile_nat mul_acc_nat_eq basename mul_acc

HOL_To_IMP_Minus_correct HTHN.mul_acc_nat by (cook mode = tailcall)

compile_nat HTHN.mul_eq_mul_acc_nat_zero basename mul

HOL_To_IMP_Minus_correct Groups.times by cook

end

paragraph \<open>Boolean Operators\<close>

context HOL_Nat_To_IMP_Minus
begin

compile_nat True_nat_def basename true

declare_compiled_const True
  return_register "true.ret"
  argument_registers
  compiled "tailcall_to_IMP_Minus true_IMP_tailcall"

HOL_To_IMP_Minus_correct True_nat by cook

compile_nat False_nat_def basename false

declare_compiled_const False
  return_register "false.ret"
  argument_registers
  compiled "tailcall_to_IMP_Minus false_IMP_tailcall"

HOL_To_IMP_Minus_correct False_nat by cook

end

context HOL_To_HOL_Nat
begin

definition "not_nat (n :: nat) \<equiv> eq_nat n False_nat"

lemma not_nat_eq [HOL_To_IMP_finish_simps]: "not_nat n = natify (n = False_nat)"
  unfolding not_nat_def eq_nat_eq by simp

lemma Rel_nat_not_nat [Rel_nat_related]:
  "(Rel_nat ===> Rel_nat) not_nat Not"
  unfolding not_nat_eq by (intro rel_funI)
  (auto simp: Rel_nat_bool_iff natify_True_eq natify_False_eq True_nat_ne_False_nat)

end

context HOL_Nat_To_IMP_Minus
begin

compile_nat HTHN.not_nat_def basename not

declare_compiled_const HOL.Not
  return_register "not.ret"
  argument_registers "not.args.n"
  compiled "tailcall_to_IMP_Minus not_IMP_tailcall"

HOL_To_IMP_Minus_correct HTHN.not_nat by cook

end

paragraph \<open>Orders\<close>

context HOL_To_HOL_Nat
begin

lemma max_nat_eq_if: "max (x :: nat) y = (if x - y \<noteq> 0 then x else y)"
  by simp

lemma Rel_nat_max [Rel_nat_related]:
  "(Rel_nat ===> Rel_nat ===> Rel_nat) max (max :: nat \<Rightarrow> _)"
  by (intro rel_funI) (auto simp: Rel_nat_nat_eq_eq)

lemma min_nat_eq_if: "min (x :: nat) y = (if x - y \<noteq> 0 then y else x)"
  by simp

lemma Rel_nat_min [Rel_nat_related]:
  "(Rel_nat ===> Rel_nat ===> Rel_nat) min (min :: nat \<Rightarrow> _)"
  by (intro rel_funI) (auto simp: Rel_nat_nat_eq_eq)

end

context HOL_Nat_To_IMP_Minus
begin

compile_nat HTHN.max_nat_eq_if basename max

HOL_To_IMP_Minus_correct max by cook

compile_nat HTHN.min_nat_eq_if basename min

HOL_To_IMP_Minus_correct min by cook

end

paragraph \<open>More Boolean Operators\<close>

context HOL_To_HOL_Nat
begin

definition "conj_nat (x :: nat) y \<equiv> min (min x y) True_nat"

lemma conj_nat_eq [HOL_To_IMP_finish_simps]: "conj_nat x y = natify (x \<noteq> False_nat \<and> y \<noteq> False_nat)"
  unfolding conj_nat_def by (auto simp: natify_bool_def False_nat_eq_zero True_nat_def)

lemma Rel_nat_conj_nat [Rel_nat_related]:
  "(Rel_nat ===> Rel_nat ===> Rel_nat) conj_nat (\<and>)"
  unfolding conj_nat_eq by (intro rel_funI)
  (auto simp: Rel_nat_bool_iff natify_True_eq natify_False_eq True_nat_ne_False_nat)

definition "disj_nat (x :: nat) y \<equiv> min (max x y) True_nat"

lemma disj_nat_eq [HOL_To_IMP_finish_simps]: "disj_nat x y = natify (x \<noteq> False_nat \<or> y \<noteq> False_nat)"
  unfolding disj_nat_def by (auto simp: natify_bool_def False_nat_eq_zero True_nat_def)

lemma Rel_nat_disj_nat [Rel_nat_related]:
  "(Rel_nat ===> Rel_nat ===> Rel_nat) disj_nat (\<or>)"
  unfolding disj_nat_eq by (intro rel_funI)
  (auto simp: Rel_nat_bool_iff natify_True_eq natify_False_eq True_nat_ne_False_nat)

end

context HOL_Nat_To_IMP_Minus
begin

compile_nat HTHN.conj_nat_def basename conj

declare_compiled_const conj
  return_register "conj.ret"
  argument_registers "conj.args.x" "conj.args.y"
  compiled "tailcall_to_IMP_Minus conj_IMP_tailcall"

HOL_To_IMP_Minus_correct HTHN.conj_nat by cook

compile_nat HTHN.disj_nat_def basename disj

declare_compiled_const disj
  return_register "disj.ret"
  argument_registers "disj.args.x" "disj.args.y"
  compiled "tailcall_to_IMP_Minus disj_IMP_tailcall"

HOL_To_IMP_Minus_correct HTHN.disj_nat by cook

end

paragraph \<open>More Orders\<close>

context HOL_To_HOL_Nat
begin

definition "le_nat (x :: nat) y \<equiv> eq_nat (x - y) 0"

lemma le_nat_eq [HOL_To_IMP_finish_simps]: "le_nat x y = natify (x \<le> y)"
  unfolding le_nat_def eq_nat_eq by simp

lemma Rel_nat_le_nat [Rel_nat_related]:
  "(Rel_nat ===> Rel_nat ===> Rel_nat) le_nat ((\<le>) :: nat \<Rightarrow> _)"
  by (intro rel_funI)
  (auto simp: Rel_nat_nat_eq_eq Rel_nat_bool_iff le_nat_eq natify_True_eq natify_False_eq)

definition "lt_nat (x :: nat) y \<equiv> conj_nat (le_nat x y) (not_nat (eq_nat x y))"

lemma lt_nat_eq [HOL_To_IMP_finish_simps]: "lt_nat x y = natify (x < y)"
  unfolding lt_nat_def by (auto simp: natify_bool_def le_nat_eq conj_nat_eq not_nat_eq eq_nat_eq)

lemma Rel_nat_lt_nat [Rel_nat_related]:
  "(Rel_nat ===> Rel_nat ===> Rel_nat) lt_nat ((<) :: nat \<Rightarrow> _)"
  by (intro rel_funI)
  (auto simp: Rel_nat_nat_eq_eq Rel_nat_bool_iff lt_nat_eq natify_True_eq natify_False_eq)

end

context HOL_Nat_To_IMP_Minus
begin

compile_nat HTHN.le_nat_def basename le

declare_compiled_const "ord_class.less_eq"
  return_register "le.ret"
  argument_registers "le.args.x" "le.args.y"
  compiled "tailcall_to_IMP_Minus le_IMP_tailcall"

HOL_To_IMP_Minus_correct HTHN.le_nat by cook

compile_nat HTHN.lt_nat_def basename lt

declare_compiled_const "ord_class.less"
  return_register "lt.ret"
  argument_registers "lt.args.x" "lt.args.y"
  compiled "tailcall_to_IMP_Minus lt_IMP_tailcall"

HOL_To_IMP_Minus_correct HTHN.lt_nat by cook

end

paragraph \<open>Division\<close>

context HOL_To_HOL_Nat
begin

fun div_acc_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "div_acc_nat x y z = (if y = 0 then z else if x < y then z else div_acc_nat (x - y) y (z + 1))"
declare div_acc_nat.simps[simp del]

lemma div_acc_nat_eq_div_add: "div_acc_nat x y z = x div y + z"
  by (induction x y z rule: div_acc_nat.induct) (auto simp: div_acc_nat.simps div_if)

lemma div_eq_div_acc_nat_zero: "x div y = div_acc_nat x y 0"
  using div_acc_nat_eq_div_add by simp

lemma Rel_nat_div [Rel_nat_related]:
  "(Rel_nat ===> Rel_nat ===> Rel_nat) Rings.divide (divide :: nat \<Rightarrow> _)"
  by (auto simp: Rel_nat_nat_eq_eq div_acc_nat_eq_div_add)

end

context HOL_Nat_To_IMP_Minus
begin

compile_nat HTHN.div_acc_nat.simps basename div_acc

HOL_To_IMP_Minus_correct HTHN.div_acc_nat by (cook mode = tailcall)

compile_nat HTHN.div_eq_div_acc_nat_zero basename div

HOL_To_IMP_Minus_correct Rings.divide by cook

end

paragraph \<open>Datatype Encoding Functions\<close>

context HOL_Nat_To_IMP_Minus
begin

definition [compiled_IMP_Minus_const_def]:
  "suc_IMP \<equiv> Com.Assign ''suc.ret'' (V ''suc.args.x'' \<oplus> N 1)"

declare_compiled_const Suc
  return_register "suc.ret"
  argument_registers "suc.args.x"
  compiled suc_IMP

HOL_To_IMP_Minus_correct Suc
  unfolding suc_IMP_def
  by (fastforce intro: terminates_with_res_IMP_MinusI terminates_with_IMP_MinusI)

end

context HOL_To_HOL_Nat
begin

lemma pair_nat_eq_triangle_add: "pair_nat a b = triangle (a + b) + a"
  unfolding pair_nat_eq prod_encode_def by simp

lemma Rel_nat_triangle [Rel_nat_related]: "(Rel_nat ===> Rel_nat) triangle triangle"
  by (auto simp: Rel_nat_nat_eq_eq)
lemma Rel_nat_pair_nat [Rel_nat_related]:
  "(Rel_nat ===> Rel_nat ===> Rel_nat) pair_nat pair_nat"
  by (auto simp: Rel_nat_nat_eq_eq)

fun fst_acc_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "fst_acc_nat k m = (if m \<le> k then m else fst_acc_nat (Suc k) (m - Suc k))"
fun snd_nat_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "snd_nat_acc k m = (if m \<le> k then k - m else snd_nat_acc (Suc k) (m - Suc k))"
declare fst_acc_nat.simps[simp del] and snd_nat_acc.simps[simp del]

lemma app_eq_app_prod_decode_acc_if_eq_if:
  assumes "\<And>k m. f k m = (if m \<le> k then g (m, k - m) else f (Suc k) (m - Suc k))"
  shows "f k m = g (prod_decode_aux k m)"
proof (induction k m rule: prod_decode_aux.induct)
  case (1 k m)
  then show ?case by (cases "m \<le> k") (simp add: assms prod_decode_aux.simps)
qed

lemma fst_acc_nat_eq_fst_prod_decode_aux [simp]: "fst_acc_nat k m = fst (prod_decode_aux k m)"
  by (fact
    app_eq_app_prod_decode_acc_if_eq_if[where g = fst, simplified fst_conv, OF fst_acc_nat.simps])

lemma snd_nat_acc_eq_snd_prod_decode_aux [simp]: "snd_nat_acc k m = snd (prod_decode_aux k m)"
  by (fact
    app_eq_app_prod_decode_acc_if_eq_if[where g = snd, simplified snd_conv, OF snd_nat_acc.simps])

lemma fst_nat_eq_fst_acc_nat: "fst_nat m = fst_acc_nat 0 m"
  unfolding fst_nat_eq unpair_nat_eq prod_decode_def
  by (subst fst_acc_nat_eq_fst_prod_decode_aux) simp

lemma Rel_nat_fst_nat [Rel_nat_related]: "(Rel_nat ===> Rel_nat) fst_nat fst_nat"
  by (auto simp: Rel_nat_nat_eq_eq)

lemma snd_nat_eq_snd_nat_acc: "snd_nat m = snd_nat_acc 0 m"
  unfolding snd_nat_eq unpair_nat_eq prod_decode_def
  by (subst snd_nat_acc_eq_snd_prod_decode_aux) simp

lemma Rel_nat_snd_nat [Rel_nat_related]: "(Rel_nat ===> Rel_nat) snd_nat snd_nat"
  by (auto simp: Rel_nat_nat_eq_eq)

end

context HOL_Nat_To_IMP_Minus
begin

lemmas triangle_eq = triangle_def[unfolded Suc_eq_plus1]
compile_nat triangle_eq
HOL_To_IMP_Minus_correct triangle by cook

compile_nat HTHN.pair_nat_eq_triangle_add
HOL_To_IMP_Minus_correct pair_nat by cook

compile_nat HTHN.fst_acc_nat.simps
HOL_To_IMP_Minus_correct HTHN.fst_acc_nat by (cook mode = tailcall)

compile_nat HTHN.fst_nat_eq_fst_acc_nat
HOL_To_IMP_Minus_correct fst_nat by cook

compile_nat HTHN.snd_nat_acc.simps
HOL_To_IMP_Minus_correct HTHN.snd_nat_acc by (cook mode = tailcall)

compile_nat HTHN.snd_nat_eq_snd_nat_acc
HOL_To_IMP_Minus_correct snd_nat by cook

end

end
