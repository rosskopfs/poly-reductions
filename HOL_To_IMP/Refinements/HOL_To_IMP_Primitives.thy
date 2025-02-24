\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_To_IMP_Primitives
  imports
    "HOL_Nat_To_IMP.HOL_Nat_To_IMP_Tactics"
begin

context HOL_To_HOL_Nat
begin

declare transport_eq_id.partial_equivalence_rel_equivalenceI[per_intro del]
and transport_eq_restrict_id.partial_equivalence_rel_equivalence[per_intro del]

paragraph \<open>Numerals\<close>

text \<open>Natural number numerals are directly mapped to IMP constans and hence must not be compiled.\<close>
lemma Rel_nat_numeral [Rel_nat]: "((=) ===> Rel_nat) (numeral :: _ \<Rightarrow> nat) (numeral :: _ \<Rightarrow> nat)"
  unfolding Rel_nat_nat_eq_eq by auto

paragraph \<open>Equality\<close>

definition "eq_nat (n :: nat) m \<equiv> if (n - m) + (m - n) = 0 then True_nat else False_nat"

lemma eq_nat_eq_False_nat_iff [HOL_To_IMP_finish_simps]: "eq_nat x y = False_nat \<longleftrightarrow> x \<noteq> y"
 unfolding eq_nat_def by (auto simp: True_nat_ne_False_nat)

lemma Rel_nat_eq_nat [Rel_nat]: "(Rel_nat ===> Rel_nat ===> Rel_nat) eq_nat (=)"
proof (intro rel_funI)
  fix x x' and y y' :: 'a
  assume "Rel_nat x y" "Rel_nat x' y'"
  then show "Rel_nat (eq_nat x x') (y = y')"
  by (cases "y = y'") (auto simp: Rel_nat_iff_eq_natify compile_nat_type_def.Rep_inject eq_nat_def
    natify_True_eq natify_False_eq)
qed

end

context HOL_Nat_To_IMP
begin

(*remove simplification rules interfering with refinement proofs*)
declare neq0_conv[iff del, symmetric, iff] Nat.One_nat_def[simp del]
and de_Morgan_disj[simp del] de_Morgan_conj[simp del] not_imp[simp del] disj_not1[simp del]

unbundle tcom_syntax

context includes com_syntax and no com'_syntax and no tcom_syntax
begin

definition [compiled_IMP_const_def]:
  "eq_IMP \<equiv>
    ''eq.x_Sub_y'' ::= (V ''eq.arg.x'' \<ominus> V ''eq.arg.y'');;
    ''eq.y_Sub_x'' ::= (V ''eq.arg.y'' \<ominus> V ''eq.arg.x'');;
    ''eq.neq'' ::= (V ''eq.x_Sub_y'' \<oplus> V ''eq.y_Sub_x'');;
    IF ''eq.neq'' \<noteq>0
    THEN ''eq.ret'' ::= A (N False_nat)
    ELSE ''eq.ret'' ::= A (N True_nat)"

end

declare_compiled_const HTHN.eq_nat
  return_register "eq.ret"
  argument_registers "eq.arg.x" "eq.arg.y"
  compiled eq_IMP

declare_compiled_const HOL.eq
  return_register "eq.ret"
  argument_registers "eq.arg.x" "eq.arg.y"
  compiled eq_IMP

HOL_To_IMP_correct HTHN.eq_nat
  unfolding eq_IMP_def HTHN.eq_nat_def
  by (fastforce intro: terminates_with_res_IMPI terminates_with_IMPI)

end

paragraph \<open>Addition and Subtraction\<close>

context HOL_To_HOL_Nat
begin

lemma Rel_nat_add [Rel_nat]:
  "(Rel_nat ===> Rel_nat ===> Rel_nat) (+) ((+) :: nat \<Rightarrow> _)"
  by (auto simp: Rel_nat_nat_eq_eq)

lemma Rel_nat_sub [Rel_nat]:
  "(Rel_nat ===> Rel_nat ===> Rel_nat) (-) ((-) :: nat \<Rightarrow> _)"
  by (auto simp: Rel_nat_nat_eq_eq)

end

context HOL_Nat_To_IMP
begin

context includes com_syntax and no com'_syntax and no tcom_syntax
begin

definition [compiled_IMP_const_def]:
  "add_IMP \<equiv> ''add.ret'' ::= (V ''add.arg.x'' \<oplus> V ''add.arg.y'')"
definition [compiled_IMP_const_def]:
  "sub_IMP \<equiv> ''sub.ret'' ::= (V ''sub.arg.x'' \<ominus> V ''sub.arg.y'')"

end

declare_compiled_const "Groups.plus"
  return_register "add.ret"
  argument_registers "add.arg.x" "add.arg.y"
  compiled "add_IMP"

declare_compiled_const "Groups.minus"
  return_register "sub.ret"
  argument_registers "sub.arg.x" "sub.arg.y"
  compiled "sub_IMP"

HOL_To_IMP_correct Groups.plus
  unfolding add_IMP_def
  by (fastforce intro: terminates_with_res_IMPI terminates_with_IMPI)
HOL_To_IMP_correct Groups.minus
  unfolding sub_IMP_def
  by (fastforce intro: terminates_with_res_IMPI terminates_with_IMPI)

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

case_of_simps mul_acc_nat_eq : mul_acc_nat.simps
function_compile_nat mul_acc_nat_eq

lemma mul_eq_mul_acc_nat_zero: "x * y = mul_acc_nat x y 0"
  using mul_acc_nat_eq_mul_add by simp

function_compile_nat mul_eq_mul_acc_nat_zero

end

context HOL_Nat_To_IMP
begin

declare case_nat_eq_if[simp]
and case_bool_nat_def[simp]
and Rel_nat_selector_Suc[Rel_nat]

lemmas mul_acc_nat_nat_eq = HTHN.mul_acc_nat_nat_eq_unfolded[unfolded case_nat_eq_if]
compile_nat mul_acc_nat_nat_eq
HOL_To_IMP_correct HTHN.mul_acc_nat_nat by cook

compile_nat HTHN.times_nat_eq_unfolded
HOL_To_IMP_correct HTHN.times_nat by cook

end

paragraph \<open>Boolean Operators\<close>

context HOL_Nat_To_IMP
begin

compile_nat True_nat_def
HOL_To_IMP_correct True_nat by cook

compile_nat False_nat_def
HOL_To_IMP_correct False_nat by cook

end

context HOL_To_HOL_Nat
begin

lemma not_iff_eq_False: "\<not>b \<longleftrightarrow> b = False" by simp

function_compile_nat not_iff_eq_False

end

context HOL_Nat_To_IMP
begin

compile_nat HTHN.Not_nat_eq_unfolded
HOL_To_IMP_correct HTHN.Not_nat by cook

end

paragraph \<open>Orders\<close>

context HOL_To_HOL_Nat
begin

lemma max_nat_eq_if: "max (x :: nat) y = (if x - y \<noteq> 0 then x else y)"
  by simp

function_compile_nat max_nat_eq_if

lemma min_nat_eq_if: "min (x :: nat) y = (if x - y \<noteq> 0 then y else x)"
  by simp

function_compile_nat min_nat_eq_if

end

context HOL_Nat_To_IMP
begin

compile_nat HTHN.max_nat_eq_unfolded
HOL_To_IMP_correct HTHN.max_nat by cook

compile_nat HTHN.min_nat_eq_unfolded basename min
HOL_To_IMP_correct HTHN.min_nat by cook

end

paragraph \<open>More Boolean Operators\<close>

context HOL_To_HOL_Nat
begin

lemma conj_eq_if_then_else: "b1 \<and> b2 \<longleftrightarrow> (if b1 then if b2 then True else False else False)"
  by auto

function_compile_nat conj_eq_if_then_else

lemma disj_eq_if_then_else: "b1 \<or> b2 \<longleftrightarrow> (if b1 then True else if b2 then True else False)"
  by auto

function_compile_nat disj_eq_if_then_else

end

context HOL_Nat_To_IMP
begin

compile_nat HTHN.conj_nat_eq_unfolded
HOL_To_IMP_correct HTHN.conj_nat by cook

compile_nat HTHN.disj_nat_eq_unfolded
HOL_To_IMP_correct HTHN.disj_nat by cook

end

paragraph \<open>More Orders\<close>

context HOL_To_HOL_Nat
begin

lemma le_nat_iff_sub_eq_zero: "(x :: nat) \<le> y \<longleftrightarrow> x - y = 0" by auto

function_compile_nat le_nat_iff_sub_eq_zero

lemma lt_nat_iff_le_and_ne: "(x :: nat) < y \<longleftrightarrow> x \<le> y \<and> x \<noteq> y" by auto

function_compile_nat lt_nat_iff_le_and_ne

end

context HOL_Nat_To_IMP
begin

compile_nat HTHN.less_eq_nat_eq_unfolded
HOL_To_IMP_correct HTHN.less_eq_nat by cook

compile_nat HTHN.less_nat_eq_unfolded
HOL_To_IMP_correct HTHN.less_nat by cook

end

paragraph \<open>Division\<close>

context HOL_To_HOL_Nat
begin

fun div_acc_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "div_acc_nat x y z = (if y = 0 then z else if x < y then z else div_acc_nat (x - y) y (z + 1))"
declare div_acc_nat.simps[simp del]

lemma div_acc_nat_eq_div_add: "div_acc_nat x y z = x div y + z"
  by (induction x y z rule: div_acc_nat.induct) (auto simp: div_acc_nat.simps div_if)

function_compile_nat div_acc_nat.simps

lemma div_eq_div_acc_nat_zero: "x div y = div_acc_nat x y 0"
  using div_acc_nat_eq_div_add by simp

function_compile_nat div_eq_div_acc_nat_zero

end

context HOL_Nat_To_IMP
begin

compile_nat HTHN.div_acc_nat_nat_eq_unfolded
HOL_To_IMP_correct HTHN.div_acc_nat_nat by cook

compile_nat HTHN.divide_nat_eq_unfolded
HOL_To_IMP_correct HTHN.divide_nat by cook

end

paragraph \<open>Datatype Encoding Functions\<close>

context HOL_Nat_To_IMP
begin

definition [compiled_IMP_const_def]:
  "suc_IMP \<equiv> Com.Assign ''suc.ret'' (V ''suc.arg.x'' \<oplus> N 1)"

declare_compiled_const Suc
  return_register "suc.ret"
  argument_registers "suc.arg.x"
  compiled suc_IMP

HOL_To_IMP_correct Suc unfolding suc_IMP_def
  by (fastforce intro: terminates_with_res_IMPI terminates_with_IMPI)

end

context HOL_To_HOL_Nat
begin

function_compile_nat triangle_def

lemma pair_nat_eq_triangle_add: "pair_nat a b = triangle (a + b) + a"
  unfolding pair_nat_eq prod_encode_def by simp

text \<open>We generate unconditional equations for all functions used in the construction of natural
number datatypes. This way, one can directly compile native nat-datatype functions without
an intermediate transfer step.\<close>

function_compile_nat pair_nat_eq_triangle_add
declare pair_nat_related_transfer[Rel_nat del]

lemma pair_nat_eq_triangle_nat: "pair_nat a b = triangle_nat (a + b) + a"
proof -
  from pair_nat_related_transfer have "pair_nat_nat = pair_nat"
    unfolding Rel_nat_nat_eq_eq by (simp add: rel_fun_eq)
  with Rel_nat_nat_eq_eq pair_nat_nat_eq_unfolded show ?thesis by auto
qed

lemma Rel_nat_pair_nat [Rel_nat]: "(Rel_nat ===> Rel_nat ===> Rel_nat) pair_nat pair_nat"
  unfolding Rel_nat_nat_eq_eq by (simp add: rel_fun_eq)

end

context HOL_Nat_To_IMP
begin

compile_nat HTHN.triangle_nat_eq_unfolded
HOL_To_IMP_correct HTHN.triangle_nat by cook

compile_nat HTHN.pair_nat_eq_triangle_nat
HOL_To_IMP_correct pair_nat by cook

end

context HOL_To_HOL_Nat
begin

fun fst_acc_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "fst_acc_nat k m = (if m \<le> k then m else fst_acc_nat (Suc k) (m - Suc k))"
fun snd_acc_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "snd_acc_nat k m = (if m \<le> k then k - m else snd_acc_nat (Suc k) (m - Suc k))"
declare fst_acc_nat.simps[simp del] and snd_acc_nat.simps[simp del]

function_compile_nat fst_acc_nat.simps
function_compile_nat snd_acc_nat.simps

lemma app_eq_app_prod_decode_acc_if_eq_if:
  assumes "\<And>k m. f k m = (if m \<le> k then g (m, k - m) else f (Suc k) (m - Suc k))"
  shows "f k m = g (prod_decode_aux k m)"
proof (induction k m rule: prod_decode_aux.induct)
  case (1 k m)
  then show ?case by (cases "m \<le> k") (simp_all add: assms prod_decode_aux.simps)
qed

lemma fst_acc_nat_eq_fst_prod_decode_aux: "fst_acc_nat k m = fst (prod_decode_aux k m)"
  by (fact
    app_eq_app_prod_decode_acc_if_eq_if[where g = fst, unfolded fst_conv, OF fst_acc_nat.simps])

lemma snd_acc_nat_eq_snd_prod_decode_aux: "snd_acc_nat k m = snd (prod_decode_aux k m)"
  by (fact
    app_eq_app_prod_decode_acc_if_eq_if[where g = snd, unfolded snd_conv, OF snd_acc_nat.simps])

lemma fst_nat_eq_fst_acc_nat: "fst_nat m = fst_acc_nat 0 m"
  unfolding fst_nat_eq unpair_nat_eq prod_decode_def
  by (subst fst_acc_nat_eq_fst_prod_decode_aux) simp

lemma snd_nat_eq_snd_acc_nat: "snd_nat m = snd_acc_nat 0 m"
  unfolding snd_nat_eq unpair_nat_eq prod_decode_def
  by (subst snd_acc_nat_eq_snd_prod_decode_aux) simp

function_compile_nat fst_nat_eq_fst_acc_nat
declare fst_nat_related_transfer[Rel_nat del]

lemma fst_nat_eq_fst_acc_nat_nat: "fst_nat n = fst_acc_nat_nat 0 n"
proof -
  from fst_nat_related_transfer have "fst_nat_nat = fst_nat"
    unfolding Rel_nat_nat_eq_eq by (simp add: rel_fun_eq)
  with Rel_nat_nat_eq_eq fst_nat_nat_eq_unfolded show ?thesis by auto
qed

lemma Rel_nat_fst_nat [Rel_nat]: "(Rel_nat ===> Rel_nat) fst_nat fst_nat"
  unfolding Rel_nat_nat_eq_eq by (simp add: rel_fun_eq)

function_compile_nat snd_nat_eq_snd_acc_nat

end

context HOL_Nat_To_IMP
begin

compile_nat HTHN.fst_acc_nat_nat_eq_unfolded
HOL_To_IMP_correct HTHN.fst_acc_nat_nat by cook

compile_nat HTHN.snd_acc_nat_nat_eq_unfolded
HOL_To_IMP_correct HTHN.snd_acc_nat_nat by cook

compile_nat HTHN.fst_nat_eq_fst_acc_nat_nat
HOL_To_IMP_correct fst_nat by cook

compile_nat HTHN.snd_nat_nat_eq_unfolded
HOL_To_IMP_correct HTHN.snd_nat_nat by cook

end

context HOL_To_HOL_Nat
begin

lemma fun_pow_eq: "(f^^n) x = (case n of 0 => x | Suc n => (f^^n) (f x))"
  by (simp add: case_nat_eq_if)

lemma nat_selector_eq: "nat_selector nargs arg n =
  (let x = (snd_nat ^^ (arg + 1)) n in if arg + 1 < nargs then fst_nat x else x)"
  unfolding nat_selector_eq by simp

definition "fun_pow_snd_nat n \<equiv> snd_nat^^n"
lemmas fun_pow_snd_nat_eq = fun_pow_eq[of _ "snd_nat", folded fun_pow_snd_nat_def]

function_compile_nat fun_pow_snd_nat_eq

lemmas nat_selector_eq_fun_pow_snd_nat = nat_selector_eq[folded fun_pow_snd_nat_def]
function_compile_nat nat_selector_eq_fun_pow_snd_nat
declare nat_selector_related_transfer[Rel_nat del]

lemma nat_selector_eq_nat: "nat_selector nargs arg n =
  (let x = fun_pow_snd_nat_nat (arg + 1) n in If_nat (less_nat (arg + 1) nargs) (fst_nat x) x)"
proof -
  from nat_selector_related_transfer have "nat_selector_nat = nat_selector"
    unfolding Rel_nat_nat_eq_eq by (simp add: rel_fun_eq)
  with Rel_nat_nat_eq_eq nat_selector_nat_eq_unfolded show ?thesis by auto
qed

lemma Rel_nat_nat_selector [Rel_nat]:
  "(Rel_nat ===> Rel_nat ===> Rel_nat ===> Rel_nat) nat_selector nat_selector"
  unfolding Rel_nat_nat_eq_eq by (simp add: rel_fun_eq)

end

context HOL_Nat_To_IMP
begin

lemmas fun_pow_snd_nat_eq = HTHN.fun_pow_snd_nat_nat_eq_unfolded[unfolded case_nat_eq_if]
compile_nat fun_pow_snd_nat_eq

HOL_To_IMP_correct HTHN.fun_pow_snd_nat_nat
  supply Rel_nat_selector_Suc[Rel_nat]
  apply (tactic \<open>HM.correct_if_IMP_tailcall_correct_tac HT.get_IMP_def @{context} 1\<close>)
  by (induction y arbitrary: ya s rule: nat.induct) (cook mode = run_finish)

compile_nat HTHN.nat_selector_eq_nat
HOL_To_IMP_correct nat_selector by cook

end

end
