
(* Missing file in theory import *)

theory IMP_Minus_Common_Funs_Nat
  imports "../../IMP-/IMP_Minus_Nat_Bijection"
begin

subsection \<open>append\<close>

text\<open>Goal of this subsection is *append_tail*, which is defined in terms
  of reverse_nat and append_acc, both of which, in turn, are defined in
  terms of -- or can be related to -- *reverse_nat_acc*.\<close>

lemma revapp: "append_acc acc xs = reverse_nat_acc acc xs"
  by(induction xs arbitrary: acc rule: append_acc.induct) simp+

(*
  append_tail xs ys
= reverse_nat       (append_acc      (reverse_nat       xs) ys)
= reverse_nat       (reverse_nat_acc (reverse_nat       xs) ys)
= reverse_nat_acc 0 (reverse_nat_acc (reverse_nat_acc 0 xs) ys)
*)

(* Registers:
e: xs
f: ys
*)
definition append_tail_IMP_Minus where "append_tail_IMP_Minus \<equiv>
  ''a'' ::= (A (N 0)) ;;
  ''b'' ::= (A (V ''e'')) ;;
  ''append_tail'' ::= (A (V ''f'')) ;;
  reverse_nat_acc_IMP_Minus ;;
  ''a'' ::= (A (V ''reverse_nat_acc'')) ;;
  ''b'' ::= (A (V ''append_tail'')) ;;
  reverse_nat_acc_IMP_Minus ;;
  ''a'' ::= (A (N 0)) ;;
  ''b'' ::= (A (V ''reverse_nat_acc'')) ;;
  reverse_nat_acc_IMP_Minus ;;
  ''append_tail'' ::= (A (V ''reverse_nat_acc'')) ;;
  zero_variables [''a'', ''b'', ''c'', ''d'', ''e'', ''f'', ''fst_nat'', ''snd_nat'', ''cons'',
    ''triangle'', ''prod_encode'', ''reverse_nat_acc'']"

definition append_tail_IMP_Minus_time where
  "append_tail_IMP_Minus_time xs ys \<equiv>
16
+ reverse_nat_acc_IMP_Minus_time 0 xs
+ reverse_nat_acc_IMP_Minus_time (reverse_nat_acc 0 xs) ys
+ reverse_nat_acc_IMP_Minus_time 0 (reverse_nat_acc (reverse_nat_acc 0 xs) ys)
+ zero_variables_time [''a'', ''b'', ''c'', ''d'', ''e'', ''f'', ''fst_nat'', ''snd_nat'', ''cons'',
    ''triangle'', ''prod_encode'', ''reverse_nat_acc'']"

lemma append_tail_IMP_Minus_correct:
  "(append_tail_IMP_Minus, s)
    \<Rightarrow>\<^bsup>append_tail_IMP_Minus_time (s ''e'') (s ''f'')\<^esup>
  s(''a'':=0, ''b'':=0, ''c'':=0, ''d'':=0, ''e'':=0, ''f'':=0,
    ''fst_nat'':=0, ''snd_nat'':=0, ''cons'':=0,
    ''triangle'':=0, ''prod_encode'':=0, ''reverse_nat_acc'':=0,
    ''append_tail'':= append_tail (s ''e'') (s ''f''))"
  unfolding append_tail_IMP_Minus_def append_tail_IMP_Minus_time_def
  by (fastforce simp: ext reverse_nat_def revapp append_tail_def
      simp del: reverse_nat_acc.simps
      intro!: terminates_in_time_state_intro[OF Seq']
      intro: zero_variables_correct reverse_nat_acc_IMP_Minus_correct
      )+


subsection \<open>elemof\<close>

(* Registers:
  e: e
  f: list
  a: "result"
*)
definition elemof_IMP_Minus_iteration where "elemof_IMP_Minus_iteration \<equiv>
  ''a'' ::= ((V ''f'') \<ominus> (N 1)) ;;
  IMP_Minus_fst_nat ;;
  ''a'' ::= ((V ''fst_nat'') \<ominus> (V ''e'')) ;;
  ''b'' ::= ((V ''e'') \<ominus> (V ''fst_nat'')) ;;
  ''a'' ::= ((V ''a'') \<oplus> (V ''b'')) ;;
  IF ''a''\<noteq>0 THEN
    ''a'' ::= ((V ''f'') \<ominus> (N 1)) ;;
    IMP_Minus_snd_nat ;;

    ''f'' ::= (A (V ''snd_nat''))
  ELSE (
    ''a'' ::= (A (N 1));;
    ''f'' ::= (A (N 0))
  ) ;;
  zero_variables [''b'', ''c'', ''fst_nat'', ''snd_nat'']"
(*
WHILE 0/=l DO
  if hd_nat l = e then r = 1; BREAK
  else l = tl_nat l
*)

definition elemof_IMP_Minus_iteration_time where
  "elemof_IMP_Minus_iteration_time e l \<equiv>
  8 + IMP_Minus_fst_nat_time (l - 1) +
  (if e = hd_nat l then 5
  else 5 + IMP_Minus_fst_nat_time (l - 1))
  + zero_variables_time [''b'', ''c'', ''fst_nat'', ''snd_nat'']"

lemma elemof_IMP_Minus_iteration_correct:
  "(elemof_IMP_Minus_iteration, s)
    \<Rightarrow>\<^bsup>elemof_IMP_Minus_iteration_time (s ''e'') (s ''f'')\<^esup>
  s(''a'' := (if (s ''e'') = hd_nat (s ''f'') then 1 else 0),
    ''b'' := 0,
    ''c'' := 0,
    ''f'' := (if (s ''e'') = hd_nat (s ''f'') then 0 else (tl_nat (s ''f''))),
    ''fst_nat'' := 0,
    ''snd_nat'' := 0)"
proof(cases "hd_nat (s ''f'') = s ''e''")
  case True
  then show ?thesis
    unfolding elemof_IMP_Minus_iteration_def
      elemof_IMP_Minus_iteration_time_def
    by (fastforce simp: hd_nat_def
        intro!: terminates_in_time_state_intro[OF Seq']
        intro:zero_variables_correct IMP_Minus_fst_nat_correct
        )+
next
  case False
  then show ?thesis
    unfolding elemof_IMP_Minus_iteration_def
      elemof_IMP_Minus_iteration_time_def
    by (fastforce simp: hd_nat_def tl_nat_def 
        intro!: terminates_in_time_state_intro[OF Seq']
        intro: zero_variables_correct
        IMP_Minus_fst_nat_correct
        IMP_Minus_snd_nat_correct
        )+
qed


definition elemof_IMP_Minus_loop where "elemof_IMP_Minus_loop \<equiv>
  (WHILE ''f'' \<noteq>0 DO elemof_IMP_Minus_iteration)"

fun elemof_IMP_Minus_loop_time :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "elemof_IMP_Minus_loop_time e 0 = 2"
| "elemof_IMP_Minus_loop_time e l = 1 + elemof_IMP_Minus_iteration_time e l
 + elemof_IMP_Minus_loop_time e (if e = hd_nat l then 0 else (tl_nat l))"


lemma elemof_IMP_Minus_loop_correct:
  assumes "s ''a'' = 0" "s ''b'' = 0" "s ''c'' = 0" "s ''fst_nat'' = 0" "s ''snd_nat'' = 0"
  shows
    "(elemof_IMP_Minus_loop, s)
    \<Rightarrow>\<^bsup>elemof_IMP_Minus_loop_time (s ''e'') (s ''f'')\<^esup>
  s(''a'' := elemof (s ''e'') (s ''f''),
    ''b'' := 0,
    ''c'' := 0,
    ''f'' := 0,
    ''fst_nat'' := 0,
    ''snd_nat'' := 0 )"
  using assms
proof(induction "s ''e''" "s ''f''" arbitrary: s rule: elemof.induct)
  case 1
  then show ?case
  proof(cases "s ''f''")
    case 0 then show ?thesis
      unfolding elemof_IMP_Minus_loop_def
      by(auto simp: numeral_2_eq_2 1
          intro!: terminates_in_state_intro[OF Big_StepT.WhileFalse])
  next
    case (Suc nat)
    show ?thesis
    proof(cases "hd_nat (s ''f'') = s ''e''")
      case True
      then show ?thesis unfolding elemof_IMP_Minus_loop_def
        using Suc
          terminates_in_time_state_intro[OF Big_StepT.WhileTrue[of s], OF _
            elemof_IMP_Minus_iteration_correct Big_StepT.WhileFalse ]
        by simp
    next
      case False
      show ?thesis unfolding elemof_IMP_Minus_loop_def
        apply(rule terminates_in_state_intro[OF Big_StepT.WhileTrue])
            apply(simp add: Suc)
           apply(rule elemof_IMP_Minus_iteration_correct)
          apply(subst elemof_IMP_Minus_loop_def[symmetric])
          apply(rule 1(1))
        using False Suc by auto
    qed
  qed
qed



(* Registers:
  a: e
  b: l
*)
definition elemof_IMP_Minus where "elemof_IMP_Minus \<equiv>
  ''e'' ::= (A (V ''a'')) ;;
  ''f'' ::= (A (V ''b'')) ;;
  zero_variables [''a'', ''b'', ''c'', ''fst_nat'', ''snd_nat''] ;;
  elemof_IMP_Minus_loop ;;
  ''elemof'' ::= (A (V ''a'')) ;;
  zero_variables [''a'', ''b'', ''c'', ''e'', ''f'', ''fst_nat'', ''snd_nat'']"

definition elemof_IMP_Minus_time :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "elemof_IMP_Minus_time e l = 2 + 2
 + zero_variables_time [''a'', ''b'', ''c'', ''fst_nat'', ''snd_nat'']
 + elemof_IMP_Minus_loop_time e l + 2
 + zero_variables_time [''a'', ''b'', ''c'', ''e'', ''f'', ''fst_nat'', ''snd_nat'']
"

lemma elemof_IMP_Minus_correct:
  "(elemof_IMP_Minus, s)
    \<Rightarrow>\<^bsup>elemof_IMP_Minus_time (s ''a'') (s ''b'')\<^esup>
  s(''a'' := 0,
    ''b'' := 0,
    ''c'' := 0,
    ''e'' := 0,
    ''f'' := 0,
    ''fst_nat'' := 0,
    ''snd_nat'' := 0,
    ''elemof'' := elemof (s ''a'') (s ''b'')
  )"
  unfolding elemof_IMP_Minus_def elemof_IMP_Minus_time_def
  by(fastforce
      intro!: ext terminates_in_time_state_intro[OF Seq']
      intro: zero_variables_correct elemof_IMP_Minus_loop_correct
      )+


subsection \<open>remdups_tail\<close>

subsection \<open>list_from_acc\<close>

(* Registers:
acc: d
s: e
n: f
*)
definition list_from_acc_IMP_Minus_iteration where
  "list_from_acc_IMP_Minus_iteration \<equiv>
  cons_IMP_Minus (V ''e'') (V ''d'') ;;
  ''d'' ::= (A (V ''cons'')) ;;
  ''e'' ::= ((V ''e'') \<oplus> (N 1)) ;;
  ''f'' ::= ((V ''f'') \<ominus> (N 1))
"

definition list_from_acc_IMP_Minus_iteration_time where
  "list_from_acc_IMP_Minus_iteration_time h t \<equiv>
  cons_IMP_Minus_time h t + 6
"

lemma list_from_acc_IMP_Minus_iteration_correct:
  "(list_from_acc_IMP_Minus_iteration, s)
  \<Rightarrow>\<^bsup>list_from_acc_IMP_Minus_iteration_time (s ''e'') (s ''d'') \<^esup>
    s(''a'' := 0,
      ''b'' := 0,
      ''c'' := 0,
      ''d'' := (s ''e'')##(s ''d''),
      ''e'' := (s ''e'') + 1,
      ''f'' := (s ''f'') - 1,
      ''triangle'' := 0,
      ''prod_encode'' := 0,
      ''cons'' := (s ''e'')##(s ''d'')
    )"
  unfolding list_from_acc_IMP_Minus_iteration_def list_from_acc_IMP_Minus_iteration_time_def
  by(fastforce
      intro!: terminates_in_time_state_intro[OF Seq']
      intro: cons_IMP_Minus_correct)+

fun list_from_acc_IMP_Minus_loop_time where
  "list_from_acc_IMP_Minus_loop_time acc s 0 = 2"
| "list_from_acc_IMP_Minus_loop_time acc s (Suc n) =
  1 + list_from_acc_IMP_Minus_iteration_time s acc
  + list_from_acc_IMP_Minus_loop_time (s##acc) (s+1) n"

lemma list_from_acc_loop_correct:
  assumes "s ''cons'' = s ''d''"
    "s ''a'' = 0" "s ''b'' = 0" "s ''c'' = 0"
    "s ''triangle'' = 0" "s ''prod_encode'' = 0" 
  shows "(WHILE ''f''\<noteq>0 DO list_from_acc_IMP_Minus_iteration, s)
  \<Rightarrow>\<^bsup>list_from_acc_IMP_Minus_loop_time (s ''d'') (s ''e'') (s ''f'') \<^esup>
    s(''a'' := 0,
      ''b'' := 0,
      ''c'' := 0,
      ''d'' := list_from_acc (s ''d'') (s ''e'') (s ''f''),
      ''e'' := (s ''e'') + (s ''f''),
      ''f'' := 0,
      ''triangle'' := 0,
      ''prod_encode'' := 0,
      ''cons'' := list_from_acc (s ''d'') (s ''e'') (s ''f'')
    )"
  using assms
proof(induct "s ''d''" "s ''e''" "s ''f''" arbitrary: s rule: list_from_acc.induct)
  case 1
  show ?case
  proof(cases "s ''f''")
    case 0 then show ?thesis
      by(auto simp add: 1 intro!: terminates_in_time_state_intro[OF Big_StepT.WhileFalse])
  next
    case (Suc nat)
    show ?thesis
      apply(rule terminates_in_time_state_intro[OF Big_StepT.WhileTrue])
           apply(fastforce
          simp add: 1 Suc
          intro: 1(1) list_from_acc_IMP_Minus_iteration_correct)+
      done
  qed
qed


subsection \<open>concat_acc\<close>

(*
WHILE n \<noteq> 0
  acc := append_tail (reverse_nat (hd_nat n)) acc ;
  n = tl_nat n ;

WHILE n \<noteq> 0
  $fst = hd_nat n ;             -- $ABC fst
  $rev = reverse_nat $fst ;     -- $ABCDEF fst snd cons triangle prod_encode
  $app = append_tail $rev acc ; -- $ABCDEF fst snd cons triangle prod_encode rev app
  acc := $app ;
  $snd = tl_nat n ;             -- $ABC snd
  n = $snd ;
*)

definition concat_acc_IMP_Minus_iteration where
  "concat_acc_IMP_Minus_iteration \<equiv>
  ''a'' ::= ((V ''n'') \<ominus> (N 1)) ;;
  IMP_Minus_fst_nat ;;
  ''a'' ::= (A (N 0)) ;;
  ''b'' ::= (A (V ''fst_nat'')) ;;
  reverse_nat_acc_IMP_Minus ;;
  ''e'' ::= (A (V ''reverse_nat_acc'')) ;;
  ''f'' ::= (A (V ''acc'')) ;;
  append_tail_IMP_Minus ;;
  ''acc'' ::= (A (V ''append_tail'')) ;;
  ''a'' ::= ((V ''n'') \<ominus> (N 1)) ;;
  IMP_Minus_snd_nat ;;
  ''n'' ::= (A (V ''snd_nat'')) ;;
  zero_variables [''a'', ''b'', ''c'', ''d'', ''e'', ''f'',
    ''fst_nat'', ''snd_nat'', ''cons'', ''triangle'', ''prod_encode'',
    ''reverse_nat_acc'', ''append_tail'']
  "

definition concat_acc_IMP_Minus_iteration_time where
  "concat_acc_IMP_Minus_iteration_time acc n \<equiv>
  16
+ IMP_Minus_fst_nat_time (n - 1)
+ reverse_nat_acc_IMP_Minus_time 0 (hd_nat n)
+ append_tail_IMP_Minus_time (reverse_nat_acc 0 (hd_nat n)) acc
+ IMP_Minus_fst_nat_time (n - 1)
+ zero_variables_time [''a'', ''b'', ''c'', ''d'', ''e'', ''f'',
    ''fst_nat'', ''snd_nat'', ''cons'', ''triangle'', ''prod_encode'',
    ''reverse_nat_acc'', ''append_tail'']
"

lemma concat_acc_IMP_Minus_iteration_correct:
  "(concat_acc_IMP_Minus_iteration, s)
    \<Rightarrow>\<^bsup>concat_acc_IMP_Minus_iteration_time (s ''acc'') (s ''n'')\<^esup>
  s(''a'' := 0, ''b'' := 0, ''c'' := 0, ''d'' := 0, ''e'' := 0, ''f'' := 0,
  ''fst_nat'' := 0, ''snd_nat'' := 0, ''cons'' := 0,
  ''triangle'' := 0, ''prod_encode'' := 0,
  ''reverse_nat_acc'' := 0, ''append_tail'' := 0,
  ''acc'' := append_tail (reverse_nat (hd_nat (s ''n''))) (s ''acc''),
  ''n'' := tl_nat (s ''n'')
)"
  unfolding concat_acc_IMP_Minus_iteration_def
    concat_acc_IMP_Minus_iteration_time_def
  by(fastforce simp: hd_nat_def tl_nat_def reverse_nat_def
      intro!: ext terminates_in_time_state_intro[OF Seq']
      intro: IMP_Minus_fst_nat_correct IMP_Minus_snd_nat_correct
      reverse_nat_acc_IMP_Minus_correct
      append_tail_IMP_Minus_correct
      zero_variables_correct)+

fun concat_acc_IMP_Minus_loop_time where
  "concat_acc_IMP_Minus_loop_time acc 0 = 2"
| "concat_acc_IMP_Minus_loop_time acc n = 1
+ concat_acc_IMP_Minus_iteration_time acc n
+ concat_acc_IMP_Minus_loop_time (append_tail (reverse_nat (hd_nat n)) acc) (tl_nat n)
"

lemma concat_acc_IMP_Minus_correct:
  assumes "s ''a'' = 0" "s ''b'' = 0" "s ''c'' = 0" "s ''d'' = 0" "s ''e'' = 0" "s ''f'' = 0"
    "s ''fst_nat'' = 0" "s ''snd_nat'' = 0" "s ''cons'' = 0"
    "s ''triangle'' = 0" "s ''prod_encode'' = 0"
    "s ''reverse_nat_acc'' = 0" "s ''append_tail'' = 0"
  shows "(WHILE ''n''\<noteq>0 DO concat_acc_IMP_Minus_iteration, s)
    \<Rightarrow>\<^bsup>concat_acc_IMP_Minus_loop_time (s ''acc'') (s ''n'')\<^esup>
s(''a'':=0, ''b'':=0, ''c'':=0, ''d'':=0, ''e'':=0, ''f'':=0,
''fst_nat'' := 0, ''snd_nat'' := 0, ''cons'' := 0,
  ''triangle'' := 0, ''prod_encode'' := 0,
  ''reverse_nat_acc'' := 0, ''append_tail'' := 0,
  ''acc'' := concat_acc (s ''acc'') (s ''n''),
  ''n'' := 0)"
  using assms
proof(induct "s ''acc''" "s ''n''" arbitrary: s rule: concat_acc.induct)
  case 1
  show ?case proof(cases "s ''n''")
    case 0
    then show ?thesis
      by(auto simp add: 1
          intro!: terminates_in_time_state_intro[OF Big_StepT.WhileFalse]
          )
    next
    case (Suc nat)
    show ?thesis
      apply(rule terminates_in_time_state_intro[OF Big_StepT.WhileTrue])
           apply(fastforce simp: Suc intro: 1(1) concat_acc_IMP_Minus_iteration_correct)+
      done
  qed
qed

end
