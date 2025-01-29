
text \<open>General definition of procedure for inverting certain functions f :: nat \<Rightarrow> nat TODO: Better description

  Also some locale to structure refinement process to IMP_Minus.
\<close>

(* Clean up *)
theory Inversion
  imports Primitives "Landau_Auxiliaries"
    "HOL-Library.Rewrite" "HOL-Library.Sublist" "HOL-Eisbach.Eisbach"

    "HOL-Library.Nat_Bijection" IMP_Minus.Call_By_Prefixes
    Triangle_Extensions
begin

lemma "\<not> surj (power2 :: nat \<Rightarrow> nat)"
  by (metis (full_types) One_nat_def lessI less_exp mult.right_neutral nat_less_le numerals(2) power2_eq_square sqrt_inverse_power2 floor_sqrt_unique surj_def)
(*
  Could probably generalize from nat
  assumptions in no collections so I see exactly where I need them
*)
locale inversion =
  fixes f :: "nat \<Rightarrow> nat"
  assumes inj: "inj f"
  assumes mono: "mono f"
  assumes 0: "f 0 = 0" (* I would like to get rid of this, but then the inverse is only defined *)
begin

lemma strict_mono: "strict_mono f"
  using inj mono
  by (metis injD monoD nat_less_le strict_mono_def)

lemma inc: "n \<le> f n"
  using strict_mono strict_mono_imp_increasing by blast

definition "f_inv n \<equiv> Max {m. f m \<le> n}"

lemma f_inv_aux:
  fixes n :: nat
  shows "finite {m. f m \<le> n}" and "{m. f m \<le> n} \<noteq> {}"
proof -
  { fix m
    assume "f m \<le> n"
    then have "m \<le> n"
      apply (cases m) apply simp_all
      using inc order_trans by blast
  } note ** = this
  then have "{m. f m \<le> n} \<subseteq> {m. m \<le> n}" by auto
  then show "finite {m. f m \<le> n}" by (rule finite_subset) rule
  have "f 0 \<le> n" using 0 by simp
  then show *: "{m. f m \<le> n} \<noteq> {}" by blast
qed

lemma f_inv_unique:
  assumes "f m \<le> n" "n < f (Suc m)"
  shows   "f_inv n = m"
proof -
  have "m' \<le> m" if "f m' \<le> n" for m'
  proof -
    note that
    also note assms(2)
    finally have "m' < Suc m"
      using strict_mono strict_mono_less by blast
    thus "m' \<le> m" by simp
  qed
  with \<open>f m \<le> n\<close> f_inv_aux[of n] show ?thesis unfolding f_inv_def
    by (intro antisym Max.boundedI Max.coboundedI) simp_all
qed

lemma f_nat_le_imp_le:
  fixes m n :: nat
  assumes "f m \<le> n"
  shows "m \<le> n"
proof (cases m)
  case 0
  then show ?thesis
    by simp
next
  case (Suc nat)
  then show ?thesis
    using assms inc
    using order_trans by blast
qed

(* Real proof *)
lemma f_nat_le_eq_le: "f m \<le> f n \<longleftrightarrow> m \<le> n"
  for m n :: nat
  using strict_mono by (simp add: mono strict_mono_less_eq)

(* basically linear search, delete this code equation once you have a better one *)
lemma f_inv_code_1 [code]: "f_inv n = Max (Set.filter (\<lambda>m. f m \<le> n) {0..n})"
proof -
  from f_nat_le_imp_le [of _ n] have "{m. m \<le> n \<and> f m \<le> n} = {m. f m \<le> n}" by auto
  then show ?thesis by (simp add: f_inv_def Set.filter_def)
qed

lemma f_inv_inverse_f [simp]: "f_inv (f n) = n"
proof -
  have "{m. m \<le> n} \<noteq> {}" by auto
  then have "Max {m. m \<le> n} \<le> n" by auto
  then show ?thesis
    by (auto simp add: f_inv_def f_nat_le_eq_le intro: antisym)
qed

lemma f_inv_zero [simp]: "f_inv 0 = 0"
  using f_inv_inverse_f [of 0]
  by (simp add: "0")

(* Might no longer hold
(* Now this is gettingout of hand :) *)
lemma f_inv_one [simp]: "f_inv 1 = 1"
  using f_inv_inverse_f [of 1]  sledgehammer
  by (metis "0" One_nat_def bij bij_inv_eq_iff inversion.f_inv_inverse inversion.f_inv_unique inversion.inc
      inversion_axioms linordered_nonzero_semiring_class.zero_le_one order_le_less)
*)

lemma f_gt_0: "f 1 > 0"
  by (metis inc not_one_le_zero zero_less_iff_neq_zero)

lemma "f_inv 1 \<le> f_inv 2"
  by (metis "0" Suc_0_to_numeral Suc_1 f_inv_inverse_f f_inv_unique gr0I inc less_Suc0 nat_less_le one_le_numeral)



lemma mono_f_inv: "mono f_inv"
proof
  fix m n :: nat
  have *: "0 * 0 \<le> m" by simp
  assume "m \<le> n"
  then show "f_inv m \<le> f_inv n"
    using 0 apply (auto intro!: Max_mono \<open>0 * 0 \<le> m\<close> finite_less_ub simp add: f_inv_def f_nat_le_imp_le)
    by (metis "0" le0)
qed

lemma mono_f_inv_': "m \<le> n \<Longrightarrow> f_inv m \<le> f_inv n"
  using mono_f_inv unfolding mono_def by auto

(* No longer holds :(
lemma f_inv_greater_zero_iff [simp]: "f_inv n > 0 \<longleftrightarrow> n > 0"
proof -
  have *: "0 < Max {m. f m \<le> n} \<longleftrightarrow> (\<exists>a\<in>{m. f m \<le> n}. 0 < a)"
    by (rule Max_gr_iff) (fact f_inv_aux)+
  show ?thesis
  proof
    assume "0 < f_inv n"
    then have "0 < Max {m. f m \<le> n}" by (simp add: f_inv_def)
    with * show "0 < n" by (auto dest: f_nat_le_imp_le)
  next
    assume "0 < n"
    hence "f 1 \<le> n"
    then have "f 1 \<le> n \<and> 0 < (1::nat)"
      by (metis "0" One_nat_def Suc_leI f_inv_one f_inv_unique linorder_not_le linordered_nonzero_semiring_class.zero_le_one
          order_trans zero_less_one)
    then have "\<exists>q. f q \<le> n \<and> 0 < q" ..
    with * have "0 < Max {m. f m \<le> n}" by blast
    then show "0 < f_inv n" by (simp add: f_inv_def)
  qed
qed
*)

(* No idea what this proof does, find out sometime :) *)
lemma f_inv_f_le [simp]: "f (f_inv n) \<le> n" (* FIXME tune proof *)
proof (cases "n > 0")
  case False then show ?thesis
    using mono inc 0
    by (metis f_inv_inverse_f gr0I)
next
  case True (*then have "f_inv n > 0"
    using f_inv_greater_zero_iff by blast*)
  then have "mono (times (Max {m. f m \<le> n}))"
    using Rings.mono_mult by blast
  then have *: "Max {m. f m \<le> n} * Max {m. f m \<le> n} = Max (times (Max {m. f m \<le> n}) ` {m. f m \<le> n})"
    using f_inv_aux [of n] by (rule mono_Max_commute)
  have "\<And>a. a * a \<le> n \<Longrightarrow> Max {m. m * m \<le> n} * a \<le> n"
  proof -
    fix q
    assume "q * q \<le> n"
    show "Max {m. m * m \<le> n} * q \<le> n"
    proof (cases "q > 0")
      case False then show ?thesis by simp
    next
      case True then have "mono (times q)" by (rule mono_times_nat)
      then have "q * Max {m. m * m \<le> n} = Max (times q ` {m. m * m \<le> n})"
        using sqrt_aux [of n] by (auto simp add: power2_eq_square intro: mono_Max_commute)
      then have "Max {m. m * m \<le> n} * q = Max (times q ` {m. m * m \<le> n})" by (simp add: ac_simps)
      moreover have "finite ((*) q ` {m. m * m \<le> n})"
        by (metis (mono_tags) finite_imageI finite_less_ub le_square)
      moreover have "\<exists>x. x * x \<le> n"
        by (metis \<open>q * q \<le> n\<close>)
      ultimately show ?thesis
        by simp (metis \<open>q * q \<le> n\<close> le_cases mult_le_mono1 mult_le_mono2 order_trans)
    qed
  qed
  then have "Max ((*) (Max {m. m * m \<le> n}) ` {m. m * m \<le> n}) \<le> n"
    apply (subst Max_le_iff)
      apply (metis (mono_tags) finite_imageI finite_less_ub le_square)
     apply auto
    apply (metis le0 mult_0_right)
    done
  with * show ?thesis
    using f_inv_aux Max_in by (auto simp add: f_inv_def)
qed

lemma f_inv_le: "f_inv n \<le> n"
  using f_inv_aux [of n] by (auto simp add: f_inv_def intro: f_nat_le_imp_le)

lemma Suc_f_inv_f_gt: "n < f (Suc (f_inv n))"
  using Max_ge[OF f_inv_aux(1), of "f_inv n + 1" n]
  by (cases "n < f (Suc (f_inv n))") (simp_all add: f_inv_def)

lemma le_f_inv_iff: "x \<le> f_inv y \<longleftrightarrow> f x \<le> y"
proof -
  have "x \<le> f_inv y \<longleftrightarrow> (\<exists>z. f z \<le> y \<and> x \<le> z)"
    using Max_ge_iff[OF f_inv_aux, of x y] by (simp add: f_inv_def)
  also have "\<dots> \<longleftrightarrow> f x \<le> y"
  proof safe
    fix z assume "x \<le> z" "f z \<le> y"
    thus "f x \<le> y" by (intro le_trans[of "f x" "f z" y]) (simp_all add: f_nat_le_eq_le)
  qed auto
  finally show ?thesis .
qed

lemma le_f_invI: "f x \<le> y \<Longrightarrow> x \<le> f_inv y"
  by (simp add: le_f_inv_iff)

lemma f_inv_le_iff: "f_inv y \<le> x \<longleftrightarrow> (\<forall>z. f z \<le> y \<longrightarrow> z \<le> x)"
  using Max.bounded_iff[OF f_inv_aux] by (simp add: f_inv_def)

lemma sqrt_leI:
  "(\<And>z. f z \<le> y \<Longrightarrow> z \<le> x) \<Longrightarrow> f_inv y \<le> x"
  by simp

lemma f_less_imp_less: "f x < f y \<Longrightarrow> 0 \<le> y \<Longrightarrow> x < y"
  by (simp add: less_le_not_le f_nat_le_eq_le)
lemma f_inv_Suc:
  "f_inv (Suc n) = (if \<exists>m. Suc n = f m then Suc (f_inv n) else f_inv n)"
proof cases
  assume "\<exists> m. Suc n = f m"
  then obtain m where m_def: "Suc n = f m" by blast
  then have lhs: "f_inv (Suc n) = m" by simp
  from m_def f_inv_f_le[of n]
    have "f (f_inv n) < f m" by linarith
  with f_less_imp_less have lt_m: "f_inv n < m" by blast
  from m_def Suc_f_inv_f_gt[of "n"]
    have "f m \<le> f (Suc(f_inv n))"
      by linarith
  with f_nat_le_eq_le have "m \<le> Suc (f_inv n)" by blast
  with lt_m have "m = Suc (f_inv n)" by simp
  with lhs m_def show ?thesis by metis
next
  assume asm: "\<not> (\<exists> m. Suc n = f m)"
  hence "Suc n \<noteq> f (f_inv (Suc n))" by simp
  with f_inv_f_le[of "Suc n"]
    have "f_inv (Suc n) \<le> f_inv n" by (intro le_f_invI) linarith
  moreover have "f_inv (Suc n) \<ge> f_inv n"
    by (intro monoD[OF mono_f_inv]) simp_all
  ultimately show ?thesis using asm by simp
qed

function f_inv_bisection' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "Suc L \<ge> R \<Longrightarrow> f_inv_bisection' y L R = L"
| "Suc L < R \<Longrightarrow> f ((L+R) div 2) \<le> y \<Longrightarrow> f_inv_bisection' y L R = f_inv_bisection' y ((L + R) div 2) R"
| "Suc L < R \<Longrightarrow> f ((L+R) div 2) > y \<Longrightarrow> f_inv_bisection' y L R = f_inv_bisection' y L ((L + R) div 2)"
  by force+
termination by (relation "Wellfounded.measure (\<lambda>(y,L,R) . R-L)") auto

lemma f_inv_bisection'_correct':
  "(0::nat) \<le> L \<Longrightarrow> L < R \<Longrightarrow> f L \<le> y \<Longrightarrow> y < f R \<Longrightarrow> f (f_inv_bisection' y L R) \<le> y \<and> y < f (Suc (f_inv_bisection' y L R))"
  by (induction y L R rule: f_inv_bisection'.induct) (simp_all add: le_Suc_eq)

(* This is what I would like *)
lemma f_inv_bisection'_correct'':
  assumes "(0::nat) \<le> L" "L < R" "f L \<le> y" "y < f R"
  shows "f (f_inv_bisection' y L R) \<le> y" "y < f (Suc (f_inv_bisection' y L R))"
  using assms f_inv_bisection'_correct'  by blast+

definition "f_inv_bisection y \<equiv> f_inv_bisection' y 0 (Suc y)"

lemma f_inv_bisection_correct':
  "f (f_inv_bisection y) \<le> y" "y < f (Suc (f_inv_bisection y))"
  unfolding f_inv_bisection_def apply (all \<open>rule f_inv_bisection'_correct''\<close>)
     apply (simp_all add: "0")
  using mono Suc_le_eq inc by blast+

corollary f_inv_bisection_correct: "f_inv_bisection y = f_inv y"
  by (intro f_inv_unique[symmetric] f_inv_bisection_correct')

lemmas f_inv_bisection_code[code] = f_inv_bisection_correct[symmetric]

(* Now, I can probably do refinement as well here generally *)

(* Even the timing function should be defineable without ML *)


unbundle no IMP_Minus_Minus_Com.com_syntax

end
(* I wondered a bit how much we can do with just locales, but for timing we definitely need ML,
  so that goes to students. Locale below shows what should be generated by ML code
*)
term big_step_t

locale inversion_imp = inversion +
  (* state, in this case simple, in general more difficult, find needed variables in record by analysis of tl-rec f *)
  fixes f_imp_state_in :: "'a \<Rightarrow> nat"
  fixes f_imp_state_out :: "'a \<Rightarrow> nat"
  fixes f_imp_state :: "nat \<Rightarrow> nat \<Rightarrow> 'a"

  (* Properties of state, usually provided by record/datatype package *)
  assumes f_imp_state_in[simp]: "f_imp_state_in (f_imp_state in' out) = in'"
  assumes f_imp_state_out[simp]: "f_imp_state_out (f_imp_state in' out) = out"
  assumes f_imp_state[simp]: "f_imp_state (f_imp_state_in s) (f_imp_state_in s) = s"

  (* Program on HOL level, should be translated from tl-rec f. Probably follow the _state_upd approach though *)
  fixes f_imp :: "'a \<Rightarrow> 'a"
  (* Timing function, generated from f_imp *)
  fixes f_imp_time :: "nat \<Rightarrow> 'a \<Rightarrow> nat"

  (* Correctness of f, more complicated in general, proof hopefully fairly automatic *)
  assumes f_imp_correct: "f_imp_state_out (f_imp s) = f (f_imp_state_in s)"

  (* Pull out accumulator, maybe define without directly? Provable from from f_imp_time definition, nothing special *)
  assumes f_imp_time_acc: "f_imp_time (Suc t) s = Suc (f_imp_time t s)"

  (* Variable names occuring in IMP_Minus program, of course more general for others,
    note that there might be internal vars not in the record(Which are not relevant, input/output)
    Should be generateable from f_imp
    prefix str without . for now
  *)
  fixes f_pref_str :: string
  fixes f_in_str :: string
  fixes f_out_str :: string
  assumes f_in_str_f_out_str[simp]: "f_in_str \<noteq> f_out_str"

  (* IMP_MINUS version of f_imp, translate from f_imp *)
  fixes f_IMP_Minus :: "Com.com"
  (* Extract record from IMP_Minus state, generate from record *)
  fixes f_imp_to_HOL_state :: "string \<Rightarrow> AExp.state \<Rightarrow> 'a"

  (* Provable from from f_imp_to_HOL_state definition, nothing special *)
  assumes f_imp_to_HOL_state_add_prefix:
    "f_imp_to_HOL_state (add_prefix p1 p2) S = f_imp_to_HOL_state p2 (S o (add_prefix p1))"

  (* f_imp_to_HOL_state translates correctly, probably given by definition of f_imp_to_HOL_state *)
  assumes f_imp_state_in_f_imp_to_HOL_state[simp]: "f_imp_state_in (f_imp_to_HOL_state p S) = S (add_prefix p f_in_str)"
  assumes f_imp_state_out_f_imp_to_HOL_state[simp]: "f_imp_state_out (f_imp_to_HOL_state p S) = S (add_prefix p f_out_str)"

  (* Final desired correctness result, for the proof we probably need functional/timing correctness lemmas in between
    Also should be fairly automatic, correctness part of statement is of course more general in other cases,

    proof should again be hopefully fairly automatic, problem is runtime
  *)
  assumes f_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) f_IMP_Minus, S) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = f_imp_time 0 (f_imp_to_HOL_state (p1 @ p2) S);
      s' (add_prefix (p1 @ p2) f_out_str) =
        f_imp_state_out (f_imp (f_imp_to_HOL_state (p1 @ p2) S));
      \<And>v. v \<in> vars \<Longrightarrow> S (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
begin

(* If I create a general locale struture for this, I can get theorems like this directly on the user level *)
lemma f_imp_time_acc': "f_imp_time t s = t + f_imp_time 0 s"
  by (induction t arbitrary: s) (simp_all add: f_imp_time_acc)

(* Record package not localized :( In this case I can just use a datatype instead,
  why still records btw? is there any reason? *)
datatype f_inv_bisection'_state = f_inv_bisection'_state (f_inv_bisection'_state_y: nat)
  (f_inv_bisection'_state_L: nat) (f_inv_bisection'_state_R: nat)

definition "f_inv_bisection'_imp_state_upd s = (let
    M = f_inv_bisection'_state_L s + f_inv_bisection'_state_R s;
    M = M div 2;

    f_in = M;
    f_out = 0; \<comment> \<open>For general version, just use one var\<close>
    f_inv_bisection'_f_state = f_imp_state f_in f_out;
    f_ret = f_imp f_inv_bisection'_f_state;
    M2 = f_imp_state_out f_ret;

    \<comment> \<open>Canonical way to do general (i.e. not just one assignment) branching?\<close>
    cond = M2 - f_inv_bisection'_state_y s;
    L = if cond \<noteq> 0 then f_inv_bisection'_state_L s else M;
    R = if cond \<noteq> 0 then M else f_inv_bisection'_state_R s;

    ret = f_inv_bisection'_state (f_inv_bisection'_state_y s) L R
  in
    ret)
"

(* Names in program, note that I need to differentiate different instance *)
abbreviation "f_inv_bisection'_pref \<equiv> f_pref_str @ ''inv_bisection'.''"
abbreviation "f_inv_bisection'_y_str \<equiv> ''y''"
abbreviation "f_inv_bisection'_L_str \<equiv> ''L''"
abbreviation "f_inv_bisection'_R_str \<equiv> ''R''"

function f_inv_bisection'_imp :: "f_inv_bisection'_state \<Rightarrow> f_inv_bisection'_state" where
  "f_inv_bisection'_imp s =
  (if f_inv_bisection'_state_R s - (f_inv_bisection'_state_L s + 1) \<noteq> 0 then \<comment> \<open>While L+1 < R\<close>
    (
      let
        next_iteration = f_inv_bisection'_imp (f_inv_bisection'_imp_state_upd s)
      in
        next_iteration
    )
  else
    (
      let
        ret = s
      in
        ret
    )
  )"
  by pat_completeness auto
termination (* Same termination proof as recursive version, just some additional decoration *)
  by (relation "Wellfounded.measure (\<lambda>s. f_inv_bisection'_state_R s - f_inv_bisection'_state_L s)")
    (auto simp: f_inv_bisection'_imp_state_upd_def Let_def split: if_splits)

declare f_inv_bisection'_imp.simps[simp del]

lemma f_inv_bisection'_imp_correct: "f_inv_bisection'_state_L (f_inv_bisection'_imp s)
  = f_inv_bisection' (f_inv_bisection'_state_y s) (f_inv_bisection'_state_L s) (f_inv_bisection'_state_R s)"
proof (induction s rule: f_inv_bisection'_imp.induct)
  case (1 s)
  then show ?case
    apply(subst f_inv_bisection'_imp.simps)
    apply (auto simp: f_inv_bisection'_imp_state_upd_def Let_def f_imp_correct
         split: if_splits) (* Slow, very slow, do better*)
    done
qed

function f_inv_bisection'_imp_time :: "nat \<Rightarrow> f_inv_bisection'_state \<Rightarrow> nat" where
  "f_inv_bisection'_imp_time t s =
  (if f_inv_bisection'_state_R s - (f_inv_bisection'_state_L s + 1) \<noteq> 0 then \<comment> \<open>While L+1 < R\<close>
    (
      let
        t = t + 5; \<comment> \<open>To account for while loop condition checking and difference computation\<close>
         \<comment> \<open>Computation of M\<close>

        M = f_inv_bisection'_state_L s + f_inv_bisection'_state_R s;
        t = t + 2;
        M = M div 2;
        t = t + 2;

        f_in = M;
        t = t + 2;
        f_out = 0; \<comment> \<open>For general version, just use one var\<close>
        t = t + 2;
        f_inv_bisection'_f_state = f_imp_state f_in f_out;
        f_ret = f_imp f_inv_bisection'_f_state;
        t = t + f_imp_time 0 f_inv_bisection'_f_state;
        M2 = f_imp_state_out f_ret;
        t = t + 2;

        \<comment> \<open>Canonical way to do general (i.e. not just one assignment) branching?\<close>
        cond = M2 - f_inv_bisection'_state_y s;
        t = t + 2;
        L = if cond \<noteq> 0 then f_inv_bisection'_state_L s else M;
        t = t + 3;
        R = if cond \<noteq> 0 then M else f_inv_bisection'_state_R s;
        t = t + 3;

        next_iteration = f_inv_bisection'_imp_time t (f_inv_bisection'_imp_state_upd s)
      in
        next_iteration
    )
  else
    (
      let
        t = t + 7;
        ret = t
      in
        ret
    )
  )"
  by pat_completeness auto
termination (* Same termination proof as recursive version, just some additional decoration *)
  by (relation "Wellfounded.measure (\<lambda>(t,s). f_inv_bisection'_state_R s - f_inv_bisection'_state_L s)")
    (auto simp: f_inv_bisection'_imp_state_upd_def Let_def split: if_splits)


declare f_inv_bisection'_imp_time.simps[simp del]

lemma f_inv_bisection'_imp_time_acc: "(f_inv_bisection'_imp_time (Suc t) s) = Suc (f_inv_bisection'_imp_time t s)"
proof (induction t s arbitrary: rule: f_inv_bisection'_imp_time.induct)
  case (1 t s)
  then show ?case
  proof(cases "f_inv_bisection'_state_R s - (f_inv_bisection'_state_L s + 1) \<noteq> 0")
    case True
    hence "(Suc (f_inv_bisection'_state_L s)) < f_inv_bisection'_state_R s"
      by simp
    with True show ?thesis
      apply (subst (2) f_inv_bisection'_imp_time.simps)
      apply (subst f_inv_bisection'_imp_time.simps)
      using 1 by (simp add: f_inv_bisection'_imp_state_upd_def Let_def split: if_splits)
  next
    case False
    then show ?thesis
      by (auto simp add: f_inv_bisection'_imp_time.simps split: if_splits)
  qed
qed

lemma f_inv_bisection'_imp_time_acc': "(f_inv_bisection'_imp_time t s) = t + (f_inv_bisection'_imp_time 0 s)"
  by (induction t) (auto simp add: f_inv_bisection'_imp_time_acc)
lemma f_inv_bisection'_imp_time_acc'': "NO_MATCH 0 t \<Longrightarrow> (f_inv_bisection'_imp_time t s) = t + (f_inv_bisection'_imp_time 0 s)"
  using f_inv_bisection'_imp_time_acc' .

definition f_inv_bisection'_IMP_Minus_while_condition where
  "f_inv_bisection'_IMP_Minus_while_condition \<equiv>
  ''inc'' ::= ((V f_inv_bisection'_L_str) \<oplus> (N 1));;
   ''diff'' ::= ((V f_inv_bisection'_R_str) \<ominus> (V ''inc''))"

(* Dangerous*)
abbreviation "f_prefix_str \<equiv> f_pref_str @ ''.''"

definition f_inv_bisection'_IMP_Minus_loop_body where
  "f_inv_bisection'_IMP_Minus_loop_body =
    \<comment> \<open>M = (L+R) / 2;\<close>
    ''M'' ::= ((V f_inv_bisection'_L_str) \<oplus> (V f_inv_bisection'_R_str));;
    ''M'' ::= ((V ''M'')\<then>);;

    \<comment> \<open>M*M,\<close>
    (f_prefix_str @ f_in_str) ::= A (V ''M'');;
    (f_prefix_str @ f_out_str) ::= A (N 0);;
    invoke_subprogram f_prefix_str f_IMP_Minus;;
    ''M2'' ::= A (V (f_prefix_str @ f_out_str));;

    \<comment> \<open>New left bound\<close>
    ''cond'' ::= ((V ''M2'') \<ominus> (V f_inv_bisection'_y_str));;
    (IF ''cond''\<noteq>0 THEN f_inv_bisection'_L_str ::= A (V f_inv_bisection'_L_str) ELSE f_inv_bisection'_L_str ::= A (V ''M''));;
    \<comment> \<open>New right bound\<close>
    (IF ''cond''\<noteq>0 THEN f_inv_bisection'_R_str ::= A (V ''M'') ELSE f_inv_bisection'_R_str ::= A (V f_inv_bisection'_R_str))"

definition f_inv_bisection'_IMP_Minus_after_loop where
  "f_inv_bisection'_IMP_Minus_after_loop = Com.SKIP"

definition f_inv_bisection'_IMP_Minus where
"f_inv_bisection'_IMP_Minus \<equiv>
  \<comment> \<open>if L+1 < R\<close>
  f_inv_bisection'_IMP_Minus_while_condition;;
  WHILE ''diff''\<noteq>0 DO (
    f_inv_bisection'_IMP_Minus_loop_body;;
    f_inv_bisection'_IMP_Minus_while_condition
  );;
  f_inv_bisection'_IMP_Minus_after_loop"

lemmas f_inv_bisection'_IMP_Minus_subprogram_simps =
  f_inv_bisection'_IMP_Minus_while_condition_def f_inv_bisection'_IMP_Minus_loop_body_def f_inv_bisection'_IMP_Minus_after_loop_def

definition "f_inv_bisection'_imp_to_HOL_state p s = f_inv_bisection'_state
  (s (add_prefix p f_inv_bisection'_y_str))
  (s (add_prefix p f_inv_bisection'_L_str))
  (s (add_prefix p f_inv_bisection'_R_str))"

abbreviation
  "f_inv_bisection'_IMP_vars \<equiv> {f_inv_bisection'_y_str, f_inv_bisection'_L_str, f_inv_bisection'_R_str,
  ''inc'', ''diff'', ''cond'', ''M'', ''M2''}"

lemma why_is_this_not_happening: "f_inv_bisection'_state_y
     (f_inv_bisection'_state (s (add_prefix p ''y'')) (s (add_prefix p ''L''))
       (s (add_prefix p ''R''))) = (s (add_prefix p ''y''))"
  by simp

lemma do_not_want_to_search: "n+1 = Suc n"
  by simp

lemma cond_elim: "(\<And>v . v \<in> insert w W \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v))
  \<Longrightarrow> (s (add_prefix p w) = s' (add_prefix p w) \<Longrightarrow> (\<And>v . v \<in> W \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)) \<Longrightarrow> P)
  \<Longrightarrow> P"
  by auto

lemma simp_cond1: "(\<And>v . v \<in> W \<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)) \<equiv> Trueprop (\<forall>v\<in>W . s (add_prefix p v) = s' (add_prefix p v))"
  by (rule atomize_ball)

lemma simp_cond2: "(\<forall>v\<in>insert w W . s (add_prefix p v) = s' (add_prefix p v))
  = (s (add_prefix p w) = s' (add_prefix p w) \<and> (\<forall>v\<in>W . s (add_prefix p v) = s' (add_prefix p v)))"
  by auto

lemma simp_cond3: "(\<forall>v\<in>{} . P v) = True"
  by auto

lemma "set xs \<noteq> set ys \<Longrightarrow> xs \<noteq> ys"
  by blast

(* YEAAAH! *)
lemma f_inv_bisection'_IMP_Minus_correct_function_1:
  "(invoke_subprogram p f_inv_bisection'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p f_inv_bisection'_L_str) =
       f_inv_bisection'_state_L (f_inv_bisection'_imp (f_inv_bisection'_imp_to_HOL_state p s))"
proof (induction "f_inv_bisection'_imp_to_HOL_state p s" arbitrary: s s' t rule: f_inv_bisection'_imp.induct)
  case 1
  then show ?case
  apply (subst f_inv_bisection'_imp.simps)
  apply (simp only: f_inv_bisection'_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule While_tE)
     apply (auto simp add: f_inv_bisection'_imp_state_upd_def prefix_simps Let_def
        f_inv_bisection'_imp_to_HOL_state_def f_inv_bisection'_IMP_Minus_subprogram_simps split: if_splits)[]
    apply (erule Seq_tE)+
    apply dest_com_gen


    subgoal (* This seems unproblematic *)
    apply (simp only: f_inv_bisection'_IMP_Minus_while_condition_def prefix_simps)
    apply (erule Seq_tE)+
      by (auto simp add: f_inv_bisection'_imp_to_HOL_state_def)

    subgoal premises p for x s2 y xa s2a ya xb s2b yb xc s2c yc
      thm p
      using p(4,5,8,9) apply -
      apply (simp only: f_inv_bisection'_IMP_Minus_while_condition_def f_inv_bisection'_IMP_Minus_loop_body_def prefix_simps)
      apply(erule Seq_tE)+
      apply(all \<open>erule f_IMP_Minus_correct[where vars = "f_inv_bisection'_IMP_vars"]\<close>)
      subgoal premises p  using p(24) by (auto simp add: prefix_Cons) (* Here we already see how auto gets confused by all the crap in p,
        also a free prefix made it more difficult, abuse . *)
      apply(elim If_tE)
      apply (all \<open>drule AssignD\<close>)+
         apply (all \<open>erule conjE\<close>)+
          (* All proofs the same now, instantiations maybe with simprocs *)
          subgoal premises p
          using p(1,13,15-) using p(14) apply (elim cond_elim) (* Seems to work, still need to filter garbage out *)
          apply (auto simp add: f_inv_bisection'_imp_state_upd_def f_inv_bisection'_imp_to_HOL_state_def Let_def f_imp_correct split: if_splits simp add: p(14)[of "''y''"] Cons_eq_append_conv)
          done
          subgoal premises p
          using p(1,13,15-)
          (* Full hammer, but it won't work without instantiations *)
          using p(14)[of "''M2''"] p(14)[of "''M''"] p(14)[of "''inc''"] p(14)[of "''diff''"] p(14)[of "''cond''"] p(14)[of "''y''"] p(14)[of "''L''"] p(14)[of "''R''"]
          apply (auto simp add: f_inv_bisection'_imp_state_upd_def f_inv_bisection'_imp_to_HOL_state_def Let_def f_imp_correct split: if_splits simp add: p(14)[of "''y''"] Cons_eq_append_conv)
          done
          subgoal premises p
          using p(1,13,15-)
          (* Full hammer, but it won't work without instantiations *)
          using p(14)[of "''M2''"] p(14)[of "''M''"] p(14)[of "''inc''"] p(14)[of "''diff''"] p(14)[of "''cond''"] p(14)[of "''y''"] p(14)[of "''L''"] p(14)[of "''R''"]
          apply (auto simp add: f_inv_bisection'_imp_state_upd_def f_inv_bisection'_imp_to_HOL_state_def Let_def f_imp_correct split: if_splits simp add: p(14)[of "''y''"] Cons_eq_append_conv)
          done
          subgoal premises p
          using p(1,13,15-)
          (* Full hammer, but it won't work without instantiations *)
          using p(14)[of "''M2''"] p(14)[of "''M''"] p(14)[of "''inc''"] p(14)[of "''diff''"] p(14)[of "''cond''"] p(14)[of "''y''"] p(14)[of "''L''"] p(14)[of "''R''"]
          apply (auto simp add: f_inv_bisection'_imp_state_upd_def f_inv_bisection'_imp_to_HOL_state_def Let_def f_imp_correct split: if_splits simp add: p(14)[of "''y''"] Cons_eq_append_conv)
          done
        done

      subgoal premises p for x s2 y xa s2a ya xb s2b yb xc s2c yc
      thm p
      using p(4,5,8,9) apply -
      apply (simp only: f_inv_bisection'_IMP_Minus_while_condition_def f_inv_bisection'_IMP_Minus_loop_body_def prefix_simps)
      apply(erule Seq_tE)+
      apply(all \<open>erule f_IMP_Minus_correct[where vars = "f_inv_bisection'_IMP_vars"]\<close>)
      subgoal premises p  using p(24) by (auto simp add: prefix_Cons) (* Here we already see how auto gets confused by all the crap in p,
        also a free prefix made it more difficult, abuse . *)
      apply(elim If_tE)
      apply (all \<open>drule AssignD\<close>)+
         apply (all \<open>erule conjE\<close>)+
          (* All proofs the same now, instantiations maybe with simprocs *)
          subgoal premises p
          using p(1,13,15-)
          (* Full hammer, but it won't work without instantiations *)
          using p(14)[of "''M2''"] p(14)[of "''M''"] p(14)[of "''inc''"] p(14)[of "''diff''"] p(14)[of "''cond''"] p(14)[of "''y''"] p(14)[of "''L''"] p(14)[of "''R''"]
          apply (auto simp add: f_inv_bisection'_imp_state_upd_def f_inv_bisection'_imp_to_HOL_state_def Let_def f_imp_correct split: if_splits simp add: p(14)[of "''y''"] Cons_eq_append_conv)
          done
          subgoal premises p
          using p(1,13,15-)
          (* Full hammer, but it won't work without instantiations *)
          using p(14)[of "''M2''"] p(14)[of "''M''"] p(14)[of "''inc''"] p(14)[of "''diff''"] p(14)[of "''cond''"] p(14)[of "''y''"] p(14)[of "''L''"] p(14)[of "''R''"]
          apply (auto simp add: f_inv_bisection'_imp_state_upd_def f_inv_bisection'_imp_to_HOL_state_def Let_def f_imp_correct split: if_splits simp add: p(14)[of "''y''"] Cons_eq_append_conv)
          done
          subgoal premises p
          using p(1,13,15-)
          (* Full hammer, but it won't work without instantiations *)
          using p(14)[of "''M2''"] p(14)[of "''M''"] p(14)[of "''inc''"] p(14)[of "''diff''"] p(14)[of "''cond''"] p(14)[of "''y''"] p(14)[of "''L''"] p(14)[of "''R''"]
          apply (auto simp add: f_inv_bisection'_imp_state_upd_def f_inv_bisection'_imp_to_HOL_state_def Let_def f_imp_correct split: if_splits simp add: p(14)[of "''y''"] Cons_eq_append_conv)
          done
          subgoal premises p
          using p(1,13,15-)
          (* Full hammer, but it won't work without instantiations *)
          using p(14)[of "''M2''"] p(14)[of "''M''"] p(14)[of "''inc''"] p(14)[of "''diff''"] p(14)[of "''cond''"] p(14)[of "''y''"] p(14)[of "''L''"] p(14)[of "''R''"]
          apply (auto simp add: f_inv_bisection'_imp_state_upd_def f_inv_bisection'_imp_to_HOL_state_def Let_def f_imp_correct split: if_splits simp add: p(14)[of "''y''"] Cons_eq_append_conv)
          done
        done
      done
  qed

lemma f_inv_bisection'_IMP_Minus_correct_time:
  "(invoke_subprogram p f_inv_bisection'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow> t = f_inv_bisection'_imp_time 0 (f_inv_bisection'_imp_to_HOL_state p s)"
proof (induction "f_inv_bisection'_imp_to_HOL_state p s" arbitrary: s s' t rule: f_inv_bisection'_imp.induct)
  case 1
  from "1.prems" show ?case
  apply (subst f_inv_bisection'_imp_time.simps)
  apply (simp only: f_inv_bisection'_IMP_Minus_def prefix_simps)
  apply (erule Seq_tE)+
  apply (erule While_tE_time)
     apply (auto simp add: f_inv_bisection'_imp_state_upd_def prefix_simps Let_def
        f_inv_bisection'_imp_to_HOL_state_def f_inv_bisection'_IMP_Minus_subprogram_simps f_inv_bisection'_imp_time_acc split: if_splits)[]
    apply (erule Seq_tE)+
    using "1.hyps"[unfolded f_inv_bisection'_IMP_Minus_def] apply -
    apply (simp add: add.assoc)
    apply dest_com_gen_time


    subgoal (* This seems unproblematic *)
    apply (simp only: f_inv_bisection'_IMP_Minus_while_condition_def prefix_simps)
    apply (erule Seq_tE)+
      by (auto simp add: f_inv_bisection'_imp_to_HOL_state_def)


    subgoal premises p for x s2 y xa s2a ya xb s2b yb xc s2c yc
      thm p
      using p(4,5,8,9) apply -
      apply (simp only: f_inv_bisection'_IMP_Minus_while_condition_def f_inv_bisection'_IMP_Minus_loop_body_def prefix_simps)
      apply(erule Seq_tE)+
      apply(all \<open>erule f_IMP_Minus_correct[where vars = "f_inv_bisection'_IMP_vars"]\<close>)
      subgoal premises p  using p(24) by (auto simp add: prefix_Cons) (* Here we already see how auto gets confused by all the crap in p,
        also a free prefix made it more difficult, abuse . *)
      apply(elim If_tE)
      apply (all \<open>drule AssignD\<close>)+
         apply (all \<open>erule conjE\<close>)+
          (* All proofs the same now, instantiations maybe with simprocs *)
          subgoal premises p
          using p(1,13,15-)
          (* Full hammer, but it won't work without instantiations *)
          using p(14)[of "''M2''"] p(14)[of "''M''"] p(14)[of "''inc''"] p(14)[of "''diff''"] p(14)[of "''cond''"] p(14)[of "''y''"] p(14)[of "''L''"] p(14)[of "''R''"]
          apply (auto simp add: f_inv_bisection'_imp_state_upd_def f_inv_bisection'_imp_to_HOL_state_def Let_def f_imp_correct split: if_splits simp add: p(14)[of "''y''"] Cons_eq_append_conv)
          done
          subgoal premises p
          using p(1,13,15-)
          (* Full hammer, but it won't work without instantiations *)
          using p(14)[of "''M2''"] p(14)[of "''M''"] p(14)[of "''inc''"] p(14)[of "''diff''"] p(14)[of "''cond''"] p(14)[of "''y''"] p(14)[of "''L''"] p(14)[of "''R''"]
          apply (auto simp add: f_inv_bisection'_imp_state_upd_def f_inv_bisection'_imp_to_HOL_state_def Let_def f_imp_correct split: if_splits simp add: p(14)[of "''y''"] Cons_eq_append_conv)
          done
          subgoal premises p
          using p(1,13,15-)
          (* Full hammer, but it won't work without instantiations *)
          using p(14)[of "''M2''"] p(14)[of "''M''"] p(14)[of "''inc''"] p(14)[of "''diff''"] p(14)[of "''cond''"] p(14)[of "''y''"] p(14)[of "''L''"] p(14)[of "''R''"]
          apply (auto simp add: f_inv_bisection'_imp_state_upd_def f_inv_bisection'_imp_to_HOL_state_def Let_def f_imp_correct split: if_splits simp add: p(14)[of "''y''"] Cons_eq_append_conv)
          done
          subgoal premises p
          using p(1,13,15-)
          (* Full hammer, but it won't work without instantiations *)
          using p(14)[of "''M2''"] p(14)[of "''M''"] p(14)[of "''inc''"] p(14)[of "''diff''"] p(14)[of "''cond''"] p(14)[of "''y''"] p(14)[of "''L''"] p(14)[of "''R''"]
          apply (auto simp add: f_inv_bisection'_imp_state_upd_def f_inv_bisection'_imp_to_HOL_state_def Let_def f_imp_correct split: if_splits simp add: p(14)[of "''y''"] Cons_eq_append_conv)
          done
        done

      subgoal premises p for x s2 y xa s2a ya xb s2b yb xc s2c yc
      thm p
      using p(4,5,8,9) apply -
      apply (simp only: f_inv_bisection'_IMP_Minus_while_condition_def f_inv_bisection'_IMP_Minus_loop_body_def prefix_simps)
      apply(erule Seq_tE)+
      apply(all \<open>erule f_IMP_Minus_correct[where vars = "f_inv_bisection'_IMP_vars"]\<close>)
      subgoal premises p  using p(24) by (auto simp add: prefix_Cons) (* Here we already see how auto gets confused by all the crap in p,
        also a free prefix made it more difficult, abuse . *)
      apply(elim If_tE)
      apply (all \<open>drule AssignD\<close>)+
         apply (all \<open>erule conjE\<close>)+
          (* All proofs the same now, instantiations maybe with simprocs *)
          subgoal premises p thm p
          using p(1,13,15-)
          (* Full hammer, but it won't work without instantiations *)
          using p(14)[of "''M2''"] p(14)[of "''M''"] p(14)[of "''inc''"] p(14)[of "''diff''"] p(14)[of "''cond''"] p(14)[of "''y''"] p(14)[of "''L''"] p(14)[of "''R''"]
          apply (auto simp add: f_inv_bisection'_imp_state_upd_def f_inv_bisection'_imp_to_HOL_state_def Let_def f_imp_correct split: if_splits simp add: p(14)[of "''y''"] Cons_eq_append_conv)
          by (metis f_imp_state f_imp_state_in f_imp_state_out) (* ? *)
          subgoal premises p
          using p(1,13,15-)
          (* Full hammer, but it won't work without instantiations *)
          using p(14)[of "''M2''"] p(14)[of "''M''"] p(14)[of "''inc''"] p(14)[of "''diff''"] p(14)[of "''cond''"] p(14)[of "''y''"] p(14)[of "''L''"] p(14)[of "''R''"]
          apply (auto simp add: f_inv_bisection'_imp_state_upd_def f_inv_bisection'_imp_to_HOL_state_def Let_def f_imp_correct split: if_splits simp add: p(14)[of "''y''"] Cons_eq_append_conv)

          done
          subgoal premises p
          using p(1,13,15-)
          (* Full hammer, but it won't work without instantiations *)
          using p(14)[of "''M2''"] p(14)[of "''M''"] p(14)[of "''inc''"] p(14)[of "''diff''"] p(14)[of "''cond''"] p(14)[of "''y''"] p(14)[of "''L''"] p(14)[of "''R''"]
          apply (auto simp add: f_inv_bisection'_imp_state_upd_def f_inv_bisection'_imp_to_HOL_state_def Let_def f_imp_correct split: if_splits simp add: p(14)[of "''y''"] Cons_eq_append_conv)
          done
          subgoal premises p
          using p(1,13,15-)
          (* Full hammer, but it won't work without instantiations *)
          using p(14)[of "''M2''"] p(14)[of "''M''"] p(14)[of "''inc''"] p(14)[of "''diff''"] p(14)[of "''cond''"] p(14)[of "''y''"] p(14)[of "''L''"] p(14)[of "''R''"]
          apply (auto simp add: f_inv_bisection'_imp_state_upd_def f_inv_bisection'_imp_to_HOL_state_def Let_def f_imp_correct split: if_splits simp add: p(14)[of "''y''"] Cons_eq_append_conv)
          by (metis f_imp_state f_imp_state_in f_imp_state_out) (* ? *)
          done
        done
  qed

lemma IMP_Minus_correct_effects:
  "(invoke_subprogram (p1 @ p2) prog, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>  v \<in> vars \<Longrightarrow> \<not> (prefix p2 v)
  \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)"
  using com_add_prefix_valid'' com_only_vars
  by (metis prefix_def)

lemma f_inv_bisection'_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) f_inv_bisection'_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = (f_inv_bisection'_imp_time 0 (f_inv_bisection'_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) f_inv_bisection'_L_str) =
        f_inv_bisection'_state_L (f_inv_bisection'_imp (f_inv_bisection'_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using f_inv_bisection'_IMP_Minus_correct_time f_inv_bisection'_IMP_Minus_correct_function_1
        IMP_Minus_correct_effects
  by auto


datatype f_inv_bisection_state = f_inv_bisection_state (f_inv_bisection_state_y: nat) (f_inv_bisection_state_ret: nat)

abbreviation "f_inv_bisection_prefix \<equiv> f_pref_str @ ''inv_bisection.''"
abbreviation "f_inv_bisection_y_str \<equiv> ''y''"
abbreviation "f_inv_bisection_ret_str \<equiv> ''ret''"

abbreviation
  "f_inv_bisection_IMP_vars \<equiv> {f_inv_bisection_y_str, f_inv_bisection_ret_str}"

definition "f_inv_bisection_imp_state_upd s = (let
    f_inv_bisection'_y = f_inv_bisection_state_y s;
    f_inv_bisection'_L = 0;
    f_inv_bisection'_R = Suc (f_inv_bisection_state_y s);

    f_inv_bisection_f_inv_bisection'_state = f_inv_bisection'_state f_inv_bisection'_y f_inv_bisection'_L f_inv_bisection'_R;
    f_inv_bisection'_ret = f_inv_bisection'_imp f_inv_bisection_f_inv_bisection'_state;

    f_inv_bisection_ret = f_inv_bisection'_state_L f_inv_bisection'_ret;
    ret = f_inv_bisection_state (f_inv_bisection_state_y s) f_inv_bisection_ret
  in
    ret)
"

fun f_inv_bisection_imp :: "f_inv_bisection_state \<Rightarrow> f_inv_bisection_state" where
  "f_inv_bisection_imp s =
  (let
    ret = f_inv_bisection_imp_state_upd s
  in
    ret
  )"

declare f_inv_bisection_imp.simps [simp del]

lemma f_inv_bisection_imp_correct:
   "f_inv_bisection_state_ret (f_inv_bisection_imp s) = f_inv_bisection (f_inv_bisection_state_y s)"
  by (subst f_inv_bisection_imp.simps) (auto simp: f_inv_bisection'_imp_correct f_inv_bisection_def f_inv_bisection_imp_state_upd_def
      Let_def f_inv_bisection_correct[symmetric] split: if_splits)

fun f_inv_bisection_imp_time:: "nat \<Rightarrow> f_inv_bisection_state\<Rightarrow> nat" where
  "f_inv_bisection_imp_time t s =
    (
      let
        f_inv_bisection'_y = f_inv_bisection_state_y s;
        t = t+2;
        f_inv_bisection'_L = 0;
        t = t+2;
        f_inv_bisection'_R = Suc (f_inv_bisection_state_y s);
        t = t+2;

        f_inv_bisection_f_inv_bisection'_state = f_inv_bisection'_state f_inv_bisection'_y f_inv_bisection'_L f_inv_bisection'_R;
        f_inv_bisection'_ret = f_inv_bisection'_imp f_inv_bisection_f_inv_bisection'_state;
        t = t + f_inv_bisection'_imp_time 0 f_inv_bisection_f_inv_bisection'_state;

        f_inv_bisection_ret = f_inv_bisection'_state_L f_inv_bisection'_ret;
        t = t+2;
        ret = t
      in
        ret
    )
"

lemmas [simp del] = f_inv_bisection_imp_time.simps

lemma f_inv_bisection_imp_time_acc: "(f_inv_bisection_imp_time (Suc t) s) = Suc (f_inv_bisection_imp_time t s)"
  apply(subst f_inv_bisection_imp_time.simps)
  apply(subst f_inv_bisection_imp_time.simps)
  apply (auto simp add: f_inv_bisection_imp_state_upd_def Let_def eval_nat_numeral split: if_splits)
  done

lemma f_inv_bisection_imp_time_acc_2: "(f_inv_bisection_imp_time x s) = x + (f_inv_bisection_imp_time 0 s)"
  by (induction x arbitrary: s)
     (auto simp add: f_inv_bisection_imp_time_acc f_inv_bisection_imp_state_upd_def Let_def eval_nat_numeral split: if_splits)


definition f_inv_bisection_IMP_Minus where
"f_inv_bisection_IMP_Minus \<equiv>
  (
    (f_inv_bisection'_pref @ f_inv_bisection'_y_str) ::= A (V f_inv_bisection_y_str);;
    (f_inv_bisection'_pref @ f_inv_bisection'_L_str) ::= A (N 0);;
    (f_inv_bisection'_pref @ f_inv_bisection'_R_str) ::= (V f_inv_bisection_y_str \<oplus> N 1);;

    invoke_subprogram f_inv_bisection'_pref f_inv_bisection'_IMP_Minus;;

    f_inv_bisection_ret_str ::= A (V (f_inv_bisection'_pref @ f_inv_bisection'_L_str))
  )"

definition "f_inv_bisection_imp_to_HOL_state p s = f_inv_bisection_state
  (s (add_prefix p f_inv_bisection_y_str)) (s (add_prefix p f_inv_bisection_ret_str))"


lemma f_inv_bisection_IMP_Minus_correct_function:
  "(invoke_subprogram p f_inv_bisection_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     s' (add_prefix p f_inv_bisection_ret_str) = f_inv_bisection_state_ret (f_inv_bisection_imp (f_inv_bisection_imp_to_HOL_state p s))"
  apply(subst f_inv_bisection_imp.simps)
  apply(simp only: f_inv_bisection_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply (erule Seq_tE)+
  apply(all \<open>erule f_inv_bisection'_IMP_Minus_correct[where vars = "f_inv_bisection_IMP_vars"]\<close>) (* Probably do not need this here *)
   apply simp
    (* ? *)
   apply auto[]
   apply (metis bot_nat_0.not_eq_extremum f_imp_state f_imp_state_in f_imp_state_out lessI)
   apply (metis bot_nat_0.not_eq_extremum f_imp_state f_imp_state_in f_imp_state_out lessI)
  apply (drule AssignD)+
  apply (auto simp add: f_inv_bisection_imp_state_upd_def f_inv_bisection_imp_to_HOL_state_def f_inv_bisection'_imp_to_HOL_state_def)
  done

lemma f_inv_bisection_IMP_Minus_correct_time:
  "(invoke_subprogram p f_inv_bisection_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s' \<Longrightarrow>
     t = f_inv_bisection_imp_time 0 (f_inv_bisection_imp_to_HOL_state p s)"
  apply(subst f_inv_bisection_imp_time.simps)
  apply(simp only: f_inv_bisection_IMP_Minus_def com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps invoke_subprogram_append)
  apply (erule Seq_tE)+
  apply(all \<open>erule f_inv_bisection'_IMP_Minus_correct[where vars = "f_inv_bisection_IMP_vars"]\<close>) (* Probably do not need this here *)
   apply simp
    (* ? *)
   apply auto[]
   apply (metis bot_nat_0.not_eq_extremum f_imp_state f_imp_state_in f_imp_state_out lessI)
   apply (metis bot_nat_0.not_eq_extremum f_imp_state f_imp_state_in f_imp_state_out lessI)
  apply (drule AssignD)+
  apply (auto simp add: f_inv_bisection_imp_state_upd_def f_inv_bisection_imp_to_HOL_state_def f_inv_bisection'_imp_to_HOL_state_def)
  done

lemma f_inv_bisection_IMP_Minus_correct:
  "\<lbrakk>(invoke_subprogram (p1 @ p2) f_inv_bisection_IMP_Minus, s) \<Rightarrow>\<^bsup>t\<^esup> s';
    \<And>v. v \<in> vars \<Longrightarrow> \<not> (prefix p2 v);
     \<lbrakk>t = (f_inv_bisection_imp_time 0 (f_inv_bisection_imp_to_HOL_state (p1 @ p2) s));
      s' (add_prefix (p1 @ p2) f_inv_bisection_ret_str) =
        f_inv_bisection_state_ret (f_inv_bisection_imp (f_inv_bisection_imp_to_HOL_state (p1 @ p2) s));
      \<And>v. v \<in> vars \<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\<rbrakk>
     \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using f_inv_bisection_IMP_Minus_correct_time f_inv_bisection_IMP_Minus_correct_function
        IMP_Minus_correct_effects
  by auto

end

end