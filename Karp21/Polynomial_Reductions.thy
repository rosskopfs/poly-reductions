subsection \<open>Polynomial Reductions\<close>
theory Polynomial_Reductions
  imports
    NREST.Refine_Foreach
    Reductions
    Polynomial_Growth_Functions
begin

text \<open>
A program @{term_type "c :: 'a\<Rightarrow>'b nrest"}
is a poly_reduction wrt to a reduction @{term_type "red :: 'a\<Rightarrow>'b\<Rightarrow>bool"}
and a measure for the size of the problem  @{term_type "m :: 'a \<Rightarrow> nat"}
if there is a time funtion \<open>f\<close>, such that
  \<^item> \<open>f\<close> polynomial
  \<^item> and for any \<open>pi\<close>, \<open>c\<close> calculates a correct result in time \<open>f (m pi)\<close>
\<close>
definition "ispolyred c A B ma mb = (\<exists>f p ps. \<forall>pi. c pi \<le> SPEC (\<lambda>y. y = f pi) (\<lambda>_. p (ma pi))
                              \<and>  (\<forall>pi. mb (f pi) \<le> ps (ma pi))
                                   \<and> poly p \<and> poly ps \<and> is_reduction f A B )"

definition "ispolyredd c RI RO A B ma mb = (\<exists>f p ps. \<forall>pi pi'. ((pi',pi):RI \<longrightarrow>  c pi' \<le> \<Down>RO (SPEC (\<lambda>y. y = f pi) (\<lambda>_. p (ma pi))))
                              \<and>  (\<forall>pi. mb (f pi) \<le> ps (ma pi))
                                   \<and> poly p \<and> poly ps \<and> is_reduction f A B )"

lemma ispolyredd_generalizes_ispolyred:
  "ispolyred c A B ma mb = ispolyredd c Id Id A B ma mb"
  unfolding ispolyred_def ispolyredd_def by auto

lemma ispolyredd_generalizes_ispolyredD:
  "ispolyred c A B ma mb \<Longrightarrow> ispolyredd c Id Id A B ma mb"
  using ispolyredd_generalizes_ispolyred ..


thm conc_fun_chain

lemma ispolyredd_refine:
  assumes
    1: "ispolyredd c1 RA RB A B ma mb"
      and 2: "\<And>pi' pi''. (pi'',pi')\<in>RA' \<Longrightarrow>  c' pi'' \<le> \<Down>RB' (c1 pi')"
  shows
    "ispolyredd c' (RA' O RA) (RB' O RB) A B ma mb"
proof -
  from 1 obtain f1 p1 ps1 where
     spec1: "\<And>pi pi'. (pi',pi)\<in>RA \<Longrightarrow> c1 pi' \<le> \<Down>RB (SPEC (\<lambda>y. y = f1 pi) (\<lambda>_.  (p1 (ma pi))))"
   and size1: "\<And>pi. mb (f1 pi) \<le> ps1 (ma pi)"
    and p1: "poly p1" "poly ps1" and "is_reduction f1 A B" unfolding ispolyredd_def by blast


  show ?thesis
    unfolding ispolyredd_def
    apply(rule exI[where x=f1])
    apply(rule exI[where x=p1])
    apply(rule exI[where x=ps1])
    apply safe
    subgoal  apply(rule order.trans)
       apply(rule 2) apply simp
      apply(rule order.trans)
       apply(rule nrest_Rel_mono)
      apply(rule spec1) apply simp
      apply(subst conc_fun_chain) by simp
    by fact+
qed


lemma poly_monoE:
  assumes "poly p2"
  obtains p2' where "\<And>x. p2 x \<le> p2' x" "poly p2'" "mono p2'"
  using assms by (intro that[where p2' = "make_mono p2"]) (auto simp: poly_make_mono_iff)

lemma ispolyredd_trans:
  assumes 1: "ispolyredd c1 RA RB A B ma mb"
    and 2: "ispolyredd c2 RB RC B C mb mc"
  shows
      "ispolyredd (\<lambda>a. bind (c1 a) c2) RA RC A C ma mc"
proof -
  from 1 obtain f1 p1 ps1 where
     spec1: "\<And>pi pi'. (pi',pi)\<in>RA \<Longrightarrow> c1 pi' \<le> \<Down>RB (SPEC (\<lambda>y. y = f1 pi) (\<lambda>_.  (p1 (ma pi))))"
   and size1: "\<And>pi. mb (f1 pi) \<le> ps1 (ma pi)"
    and p1: "poly p1" "poly ps1" and "is_reduction f1 A B" unfolding ispolyredd_def by blast

  from 2 obtain f2 p2 ps2 where
      spec2: "\<And>pi pi'. (pi',pi)\<in>RB \<Longrightarrow> c2 pi' \<le> \<Down>RC (SPEC (\<lambda>y. y = f2 pi) (\<lambda>_. enat (p2 (mb pi))))"
    and size2: "\<And>pi. mc (f2 pi) \<le> ps2 (mb pi)"
     and p2: "poly p2" "poly ps2" "is_reduction f2 B C" unfolding ispolyredd_def by blast

  thm spec1[unfolded SPEC_def ]
  thm spec2[unfolded SPEC_def ]

  from \<open>poly p2\<close> obtain p2' where p2'_ub: "\<And>x. p2 x \<le> p2' x" and p2'_poly: "poly p2'"
    and   p2'_mono: "\<And>i j. i\<le>j \<Longrightarrow> p2' i \<le> p2' j"
    by - (erule poly_monoE, auto simp: mono_def)

  obtain ps2' where "\<And>x. ps2 x \<le> ps2' x" and ps2'_poly: "poly ps2'"
    and   ps2'_mono: "\<And>i j. i\<le>j \<Longrightarrow> ps2 i \<le> ps2' j"
    subgoal premises that
      using \<open>poly ps2\<close>
      apply -
      apply (erule poly_monoE)
      apply (rule that)
        apply (auto simp: mono_def intro: order.trans)
      done
    done

  show ?thesis
    unfolding ispolyredd_def
    apply(rule exI[where x="f2 o f1"])
    apply(rule exI[where x="\<lambda>n. p1 n + p2' (ps1 n)"])
    apply(rule exI[where x="\<lambda>n. ps2' (ps1 n)"])
    apply safe
    subgoal unfolding SPEC_def
      apply(rule order.trans)
       apply(rule bindT_refine)
      apply (rule spec1) apply simp
       apply (rule spec2) apply simp
      apply(rule nrest_Rel_mono)
  apply(rule T_specifies_I)
      apply(vcg' \<open>-\<close> rules: T_SPEC )
      apply (auto split: if_splits)
      subgoal apply(rule order_trans[OF p2'_ub]) using size1 p2'_mono
        by auto
      done
    subgoal apply simp  apply(rule order_trans[OF size2])
      apply(rule ps2'_mono) by(rule size1)
    subgoal
      using p1 p2'_poly by(auto intro: poly_compose[unfolded comp_def])
    subgoal
      using p1 ps2'_poly by(auto intro: poly_compose[unfolded comp_def])
    subgoal
      apply(rule is_reduction_trans) by fact+
    done
qed


lemma ispolyred_trans:
  "ispolyred c1 A B ma mb \<Longrightarrow> ispolyred c2 B C mb mc
    \<Longrightarrow> ispolyred (\<lambda>a. bind (c1 a) c2) A C ma mc"
  using ispolyredd_generalizes_ispolyred ispolyredd_trans by metis

lemma ispolyredI:
  assumes
    "\<And>pi. alg pi \<le> SPEC (\<lambda>y. y = f pi) (\<lambda>_. time_f (size_from pi))"
    "\<And>pi. size_to (f pi) \<le> space_f (size_from pi)"
    "poly time_f"
    "poly space_f"
    "is_reduction f from to"
  shows "ispolyred alg from to size_from size_to"
  using assms ispolyred_def by blast


end