(*Authors: Mohammad Abdulaziz*)

theory Call_By_Prefixes
  imports IMP.Com Big_StepT Vars
begin

abbreviation add_prefix :: "string \<Rightarrow> vname \<Rightarrow> vname" where
"add_prefix p s \<equiv> p @ s"

(*type_synonym pcom = "string \<Rightarrow> com"*)

fun atomExp_add_prefix where
"atomExp_add_prefix p (N a) = N a" |
"atomExp_add_prefix p (V v) = V (add_prefix p v)"

fun aexp_add_prefix where
"aexp_add_prefix p (A a) = A (atomExp_add_prefix p a)" |
"aexp_add_prefix p (Plus a b) = Plus (atomExp_add_prefix p a) (atomExp_add_prefix p b)" |
"aexp_add_prefix p (Sub a b) = Sub (atomExp_add_prefix p a) (atomExp_add_prefix p b)"

fun com_add_prefix where
"com_add_prefix p SKIP = SKIP"
|"com_add_prefix p (Assign v aexp) = (Assign (add_prefix p v) (aexp_add_prefix p aexp))"
|"com_add_prefix p (Seq c1 c2) = (Seq (com_add_prefix p c1) (com_add_prefix p c2))"
|"com_add_prefix p (If v c1 c2) = (If (add_prefix p v) (com_add_prefix p c1) (com_add_prefix p c2))"
|"com_add_prefix p (While v c) = (While (add_prefix p v) (com_add_prefix p c))"


(*
abbreviation pcom_SKIP where "pcom_SKIP p \<equiv> SKIP"

abbreviation pcom_Assign where "pcom_Assign v aexp p \<equiv>
  Assign (add_prefix p v) (aexp_add_prefix p aexp)"

abbreviation pcom_Seq where "pcom_Seq a b p \<equiv> (a  p) ;; (b p)"

abbreviation pcom_If where "pcom_If v a b p \<equiv>
  If (add_prefix p v) (a p) (b p)"

abbreviation pcom_While where "pcom_While v a p \<equiv> While (add_prefix p v) (a p)"

abbreviation write_subprogram_param where "write_subprogram_param p' a  b \<equiv>
  (\<lambda>p. Assign (add_prefix (p' @ p) a) (aexp_add_prefix p b))"

abbreviation read_subprogram_param where "read_subprogram_param a p' b \<equiv>
  (\<lambda>p. Assign (add_prefix p a) (aexp_add_prefix (p' @ p) b))"

abbreviation read_write_subprogram_param where "read_write_subprogram_param p' a p'' b \<equiv>
  (\<lambda>p. Assign (add_prefix (p' @ p) a) (aexp_add_prefix (p'' @ p) b))"

unbundle no com_syntax

open_bundle pcom_syntax
begin
notation pcom_SKIP ("SKIP" [] 61) and
         pcom_Assign ("_ ::= _" [1000, 61] 61) and
         write_subprogram_param ("[_] _ ::= _" [1000, 61, 61] 61) and
         read_subprogram_param ("_ ::= [_] _" [1000, 61, 61] 61) and
         read_write_subprogram_param ("[_] _ ::= [_] _" [1000, 61, 61, 61] 61) and
         pcom_Seq ("_;;/ _"  [60, 61] 60) and
         pcom_If ("(IF _/\<noteq>0 THEN _/ ELSE _)"  [0, 0, 61] 61) and
         pcom_While ("(WHILE _/\<noteq>0 DO _)"  [0, 61] 61)
end
*)

lemma atomExp_add_prefix_valid: "(\<And>v. v \<in> set (vars x1) \<Longrightarrow> s1 v = s1' (add_prefix p v)) \<Longrightarrow>
          atomVal x1 s1 = atomVal (atomExp_add_prefix p x1) s1'"
  by (cases x1) auto

lemma aexp_add_prefix_valid: "(\<And>v. v \<in> set (vars aexp) \<Longrightarrow> s1 v = s1' (add_prefix p v)) \<Longrightarrow>
       aval aexp s1 = aval (aexp_add_prefix p aexp) s1'"
  by (cases aexp) (auto simp: atomExp_add_prefix_valid)

lemma atomExp_add_prefix_valid': "v \<in> set (vars (atomExp_add_prefix p x1)) \<Longrightarrow> \<exists>v'. v = p @ v'"
  by (cases x1) (auto simp:)

lemma aexp_add_prefix_valid':"v \<in> set (vars (aexp_add_prefix p aexp)) \<Longrightarrow> \<exists>v'. v = p @ v'"
  by (cases aexp) (auto simp: atomExp_add_prefix_valid')

lemma com_add_prefix_valid': "v \<in> set (vars (com_add_prefix p c)) \<Longrightarrow> \<exists>v'. v = p @ v'"
  by (induction p c rule: com_add_prefix.induct) (auto simp: aexp_add_prefix_valid')

lemma atomExp_add_prefix_valid'': "add_prefix p1 v \<in> set (vars (atomExp_add_prefix (p1 @ p2) x1)) \<Longrightarrow> \<exists>v'. v = p2 @ v'"
  by (cases x1) (auto simp:)

lemma aexp_add_prefix_valid'':"add_prefix p1 v \<in> set (vars (aexp_add_prefix (p1 @ p2) aexp)) \<Longrightarrow> \<exists>v'. v = p2 @ v'"
  by (cases aexp) (auto simp: atomExp_add_prefix_valid'')


lemma com_add_prefix_valid'': "add_prefix p1 v \<in> set (vars (com_add_prefix (p1 @ p2) c)) \<Longrightarrow> \<exists>v'. v = p2 @ v'"
  by (induction "p1 @ p2" c arbitrary: p1 p2 rule: com_add_prefix.induct) (auto simp: aexp_add_prefix_valid'')

lemma com_add_prefix_valid_subset: "add_prefix p1 v \<in> set (vars (com_add_prefix (p1 @ p2) c)) \<Longrightarrow> set p2 \<subseteq> set v"
  using com_add_prefix_valid''
  by (metis set_append sup_ge1)

abbreviation invoke_subprogram
  where "invoke_subprogram \<equiv> com_add_prefix"

lemma atomExp_add_prefix_append: "atomExp_add_prefix p1 (atomExp_add_prefix p2 x1) = atomExp_add_prefix (add_prefix p1 p2) x1"
  by (cases x1) auto

lemma aexp_add_prefix_append: "aexp_add_prefix p1 (aexp_add_prefix p2 aexp) = (aexp_add_prefix (add_prefix p1 p2) aexp)"
  by (cases aexp) (auto simp: atomExp_add_prefix_append)

lemma invoke_subprogram_append: "invoke_subprogram p1 (invoke_subprogram p2 c) = (invoke_subprogram (p1 @ p2) c)"
  by (induction "(p1 @ p2)" c arbitrary: p1 p2 rule: com_add_prefix.induct) (auto simp: aexp_add_prefix_append)

lemmas prefix_simps = com_add_prefix.simps aexp_add_prefix.simps atomExp_add_prefix.simps
                      invoke_subprogram_append

end