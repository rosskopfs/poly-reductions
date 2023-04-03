
(*
  IMP_Minus_Nat_Bijection is now Primities_IMP_Minus
  It was not updated to use the new format... 
  In particular the "letification" step is missing
  TODO: Change everything to fit this

*)

theory IMP_Minus_Max_Constant_IMP_Minus
  imports IMP_Minus_Max_Constant_Nat
    "IMP-_To_IMP--/Primitives_IMP_Minus"
    (* "../../IMP-/IMP_Minus_Nat_Bijection" This theory does not exist... Search for it*)
begin

unbundle IMP_Minus_Minus_Com.no_com_syntax

definition atomExp_to_constant_IMP_Minus where "atomExp_to_constant_IMP_Minus \<equiv>
  ''atomExp_to_constant'' ::= (A (V ''a'')) ;;
  fst'_IMP_Minus ;;
  ''a'' ::= (A (V ''atomExp_to_constant'')) ;;
  snd'_IMP_Minus ;;
  (IF ''fst_nat'' \<noteq>0 
  THEN 
    ''atomExp_to_constant'' ::= (A (V ''snd_nat''))  
  ELSE
    ''atomExp_to_constant'' ::=  (A (N 0)));;
  ''fst_nat'' ::= (A (N 0)) ;;
  ''snd_nat'' ::= (A (N 0))"

definition atomExp_to_constant_IMP_Minus_time where "atomExp_to_constant_IMP_Minus_time x \<equiv>
  11 + 2 * fst'_imp_time x"

(*lemma atomExp_to_constant_IMP_Minus_time_polynomial: "poly atomExp_to_constant_IMP_Minus_time"*)

lemma atomExp_to_constant_IMP_Minus_correct:
  "(atomExp_to_constant_IMP_Minus, s) \<Rightarrow>\<^bsup>atomExp_to_constant_IMP_Minus_time (s ''a'')\<^esup> 
    s(''a'' := 0,
      ''b'' := 0,
      ''c'' := 0,
      ''fst_nat'' := 0,
      ''snd_nat'' := 0,
      ''atomExp_to_constant'' := atomExp_to_constant_tail (s ''a''))"
  apply(cases "fst_nat (s ''a'')")
  unfolding atomExp_to_constant_IMP_Minus_def atomExp_to_constant_tail_def
    atomExp_to_constant_nat_def atomExp_to_constant_IMP_Minus_time_def
  by (fastforce 
      intro!: terminates_in_state_intro[OF Seq]
      IMP_Minus_fst_nat_correct      
      IMP_Minus_snd_nat_correct)+

definition aexp_max_constant_IMP_Minus where "aexp_max_constant_IMP_Minus \<equiv> 
  ''aexp_max_constant'' ::= (A (V ''a'')) ;;

  ''a'' ::= (A (N 1)) ;;
  ''b'' ::= (A (V ''aexp_max_constant'')) ;;
  nth_nat_IMP_Minus ;;
  
  ''a'' ::= (A (V ''nth_nat'')) ;;
  atomExp_to_constant_IMP_Minus ;;
  
  ''a'' ::= (A (N 2)) ;;
  ''b'' ::= (A (V ''aexp_max_constant'')) ;;
  nth_nat_IMP_Minus ;;
  
  ''a'' ::= (A (V ''nth_nat'')) ;;
  ''nth_nat'' ::= (A (V ''atomExp_to_constant'')) ;;
  atomExp_to_constant_IMP_Minus ;;

  ''a'' ::= ((V ''aexp_max_constant'') \<ominus> (N 1)) ;;
  IMP_Minus_fst_nat ;;

  ''a'' ::= ((N 3) \<ominus> (V ''fst_nat'')) ;;
  IF ''a'' \<noteq>0 
  THEN
  (
    IF ''fst_nat'' \<noteq>0
    THEN
      ''b'' ::= (A (V ''atomExp_to_constant''))
    ELSE
      ''b'' ::= (A (V ''nth_nat''))
  )
  ELSE
  (
    IF ''fst_nat'' \<noteq>0
    THEN
      ''b'' ::= (A (V ''nth_nat''))
    ELSE
      ''b'' ::= (A (V ''nth_nat''))
  );;

  ''a'' ::= (A (V ''nth_nat'')) ;;

  IMP_Minus_max_a_min_b ;;
  ''aexp_max_constant'' ::= (A (V ''a'')) ;;
  ''a'' ::= (A (N 0)) ;; 
  ''b'' ::= (A (N 0)) ;;
  ''nth_nat'' ::= (A (N 0)) ;;
  ''atomExp_to_constant'' ::= (A (N 0)) ;;
  ''fst_nat'' ::= (A (N 0))"

definition aexp_max_constant_IMP_Minus_time where "aexp_max_constant_IMP_Minus_time x \<equiv>
  38 + nth_nat_IMP_Minus_time 1 x + atomExp_to_constant_IMP_Minus_time (nth_nat 1 x)
  + nth_nat_IMP_Minus_time 2 x +  atomExp_to_constant_IMP_Minus_time (nth_nat 2 x)
  + IMP_Minus_fst_nat_time (x - 1) + 11" 


lemma aexp_max_constant_IMP_Minus_correct:
  "(aexp_max_constant_IMP_Minus, s) 
    \<Rightarrow>\<^bsup>aexp_max_constant_IMP_Minus_time (s ''a'')\<^esup>
    s(''a'' := 0,
      ''b'' := 0,
      ''c'' := 0,
      ''fst_nat'' := 0,
      ''snd_nat'' := 0,
      ''nth_nat'' := 0,
      ''atomExp_to_constant'' := 0,
      ''aexp_max_constant'' := aexp_max_constant_tail (s ''a''))"
  unfolding aexp_max_constant_IMP_Minus_def aexp_max_constant_IMP_Minus_time_def
    aexp_max_constant_tail_def
  apply(cases "3 - fst_nat (s ''a'' - Suc 0)"; cases "fst_nat (s ''a'' - Suc 0)")
     apply simp
  apply(fastforce simp: numeral_eq_Suc hd_nat_def 
        intro!: terminates_in_time_state_intro[OF Seq]
        atomExp_to_constant_IMP_Minus_correct
        nth_nat_IMP_Minus_correct
        IMP_Minus_max_a_min_b_correct
        IMP_Minus_fst_nat_correct)
  (*apply(fastforce simp: numeral_eq_Suc hd_nat_def 
        intro!: terminates_in_time_state_intro[OF Seq]
        atomExp_to_constant_IMP_Minus_correct
        nth_nat_IMP_Minus_correct
        IMP_Minus_max_a_min_b_correct
        IMP_Minus_fst_nat_correct)*)
  subgoal
    by(fastforce simp: numeral_eq_Suc hd_nat_def 
        intro!: terminates_in_time_state_intro[OF Seq]
        atomExp_to_constant_IMP_Minus_correct
        nth_nat_IMP_Minus_correct
        IMP_Minus_max_a_min_b_correct
        IMP_Minus_fst_nat_correct)
  subgoal
    by(fastforce simp: numeral_eq_Suc hd_nat_def 
        intro!: terminates_in_time_state_intro[OF Seq]
        atomExp_to_constant_IMP_Minus_correct
        nth_nat_IMP_Minus_correct
        IMP_Minus_max_a_min_b_correct
        IMP_Minus_fst_nat_correct)
  done


definition add_res_nat_first_part where "add_res_nat_first_part \<equiv>
  ''d'' ::= (A (V ''a'')) ;;
  ''e'' ::= (A (V ''b'')) ;;

  ''a'' ::= ((V ''e'') \<ominus> (N 1)) ;;
  IMP_Minus_fst_nat ;;
  ''f'' ::= (A (V ''fst_nat'')) ;;

  ''a'' ::= ((V ''e'') \<ominus> (N 1)) ;;
  IMP_Minus_snd_nat ;;
  ''g'' ::= (A (V ''snd_nat'')) ;;

  ''a'' ::= ((V ''f'') \<ominus> (N 1)) ;;
  IMP_Minus_fst_nat ;;
  ''h'' ::= (A (V ''fst_nat'')) ;;

  ''a'' ::= (A (N (Suc 0))) ;;
  ''b'' ::= (A (V ''f'')) ;;
  nth_nat_IMP_Minus ;;
  ''i'' ::= (A (V ''nth_nat'')) ;;

  ''a'' ::= (A (N (Suc (Suc 0)))) ;;
  ''b'' ::= (A (V ''f'')) ;;
  nth_nat_IMP_Minus ;;
  ''j'' ::= (A (V ''nth_nat'')) ;;

  ''a'' ::= (A (N (Suc (Suc (Suc 0))))) ;;
  ''b'' ::= (A (V ''f'')) ;;
  nth_nat_IMP_Minus"

definition add_res_nat_first_part_time where "add_res_nat_first_part_time n s \<equiv>
  (let h = hd_nat s in
    32 + 2 * IMP_Minus_fst_nat_time (s - 1) + IMP_Minus_fst_nat_time (h - 1)
    + nth_nat_IMP_Minus_time (Suc 0) h + nth_nat_IMP_Minus_time (Suc (Suc 0)) h
    + nth_nat_IMP_Minus_time (Suc (Suc (Suc 0))) h)"

lemma add_res_nat_first_part_correct:
  "(add_res_nat_first_part, s) \<Rightarrow>\<^bsup>add_res_nat_first_part_time (s ''a'') (s ''b'')\<^esup>
    (let h = hd_nat (s ''b''); 
         t = tl_nat (s ''b''); 
         c = hd_nat h;  
         e1 = nth_nat (Suc 0) h ; 
         e2 = nth_nat (Suc (Suc 0)) h; 
         e3 = nth_nat (Suc (Suc (Suc 0))) h in 
       s(''a'' := 0,
         ''b'' := 0,
         ''c'' := 0,
         ''d'' := s ''a'',
         ''e'' := s ''b'',
         ''f'' := h,
         ''g'' := t,
         ''h'' := c,
         ''i'' := e1,
         ''j'' := e2,
         ''fst_nat'' := 0,
         ''snd_nat'' := 0,
         ''nth_nat'' := e3))"
  unfolding Let_def add_res_nat_first_part_def add_res_nat_first_part_time_def hd_nat_def tl_nat_def
  by (fastforce intro: terminates_in_time_state_intro[OF Seq] 
      terminates_in_state_intro[OF nth_nat_IMP_Minus_correct]
      IMP_Minus_fst_nat_correct IMP_Minus_snd_nat_correct)

definition add_res_nat_second_part where "add_res_nat_second_part \<equiv>
  ''k'' ::= (A (V ''d'')) ;;

  cons_list_IMP_Minus [N 7, V ''k'', N 0] ;;   
  cons_IMP_Minus (V ''cons'') (N 0) ;;
  ''l'' ::= (A (V ''cons'')) ;;

  cons_list_IMP_Minus [N 3, V ''i'', V ''j'', V ''k'', N 0] ;;
  cons_IMP_Minus (V ''cons'') (V ''g'') ;;
  ''m'' ::= (A (V ''cons'')) ;;
  
  cons_list_IMP_Minus [N 4, V ''i'', V ''j'', V ''nth_nat'', V ''k'', N 0] ;;
  cons_IMP_Minus (V ''cons'') (V ''g'') ;;
  ''n'' ::= (A (V ''cons'')) ;;

  cons_list_IMP_Minus [N 6, V ''i'', V ''k'', N 0] ;;
  cons_IMP_Minus (V ''cons'') (V ''g'') ;;

  ''f'' ::= (A (N 0)) ;;
  ''g'' ::= (A (N 0)) ;;
  ''i'' ::= (A (N 0)) ;;
  ''j'' ::= (A (N 0)) ;;
  ''nth_nat'' ::= (A (N 0)) "

definition add_res_nat_second_part_time where "add_res_nat_second_part_time n s \<equiv>
  (let h = hd_nat s; 
       t = tl_nat s; 
       c = hd_nat h;  
       e1 = nth_nat (Suc 0) h ; 
       e2 = nth_nat (Suc (Suc 0)) h; 
       e3 = nth_nat (Suc (Suc (Suc 0))) h;
       l1 = [7, n, 0];
       l2 = [3, e1, e2, n, 0];
       l3 = [4, e1, e2, e3, n, 0];
       l4 = [6, e1, n, 0]
    in 
      18 + cons_list_IMP_Minus_time l1 + cons_list_IMP_Minus_time l2 
         + cons_list_IMP_Minus_time l3 + cons_list_IMP_Minus_time l4
         + cons_IMP_Minus_time (cons_list l1) 0 + cons_IMP_Minus_time (cons_list l2) t
         + cons_IMP_Minus_time (cons_list l3) t + cons_IMP_Minus_time (cons_list l4) t)"

lemma add_res_nat_second_part_correct:  
  "(add_res_nat_first_part ;; add_res_nat_second_part, s) 
    \<Rightarrow>\<^bsup>add_res_nat_first_part_time (s ''a'') (s ''b'') 
      + add_res_nat_second_part_time (s ''a'') (s ''b'') \<^esup>
    (let h = hd_nat (s ''b''); 
       t = tl_nat (s ''b''); 
       c = hd_nat h;  
       e1 = nth_nat (Suc 0) h ; 
       e2 = nth_nat (Suc (Suc 0)) h; 
       e3 = nth_nat (Suc (Suc (Suc 0))) h;
       l1 = [7, s ''a'', 0];
       l2 = [3, e1, e2, s ''a'', 0];
       l3 = [4, e1, e2, e3, s ''a'', 0];
       l4 = [6, e1, s ''a'', 0]
    in 
      s(''a'' := 0,
        ''b'' := 0,
        ''c'' := 0,
        ''d'' := 0,
        ''e'' := s ''b'',
        ''f'' := 0,
        ''g'' := 0,
        ''h'' := c,
        ''i'' := 0,
        ''j'' := 0,
        ''fst_nat'' := 0,
        ''snd_nat'' := 0,
        ''nth_nat'' := 0,
        ''k'' := s ''a'',
        ''l'' := (cons_list l1) ## 0,
        ''m'' := (cons_list l2) ## t,
        ''n'' := (cons_list l3) ## t,
        ''cons'' := (cons_list l4) ## t,
        ''triangle'' := 0,
        ''prod_encode'' := 0))"
  apply(rule terminates_in_state_intro[OF Seq'[OF add_res_nat_first_part_correct]])
  unfolding add_res_nat_second_part_def add_res_nat_second_part_time_def Let_def
  by (fastforce intro: cons_IMP_Minus_correct cons_list_IMP_Minus_correct)+

definition add_res_nat_third_part where "add_res_nat_third_part \<equiv>
  IF ''e'' \<noteq>0
  THEN
  (
    ''a'' ::= ((V ''h'') \<ominus> (N 1)) ;;
    IF ''a'' \<noteq>0
    THEN
    (
      ''a'' ::= ((V ''h'') \<ominus> (N 3)) ;;
      IF ''a'' \<noteq>0
      THEN
      (
        ''a'' ::= ((V ''h'') \<ominus> (N 4)) ;;
        IF ''a'' \<noteq>0
        THEN
        (
           ''a'' ::= ((V ''h'') \<ominus> (N 5)) ;;
           IF ''a'' \<noteq>0
           THEN
           (
            ''add_res'' ::= (A (V ''l''))
           )
           ELSE
           (
            ''add_res'' ::= (A (V ''cons''))
           )
        )
        ELSE
        (
          ''add_res'' ::= (A (V ''l'')) ;;
          Com.SKIP ;; Com.SKIP ;; Com.SKIP
        )
      )
      ELSE
      (
         ''a'' ::= ((V ''h'') \<ominus> (N 2)) ;;
         IF ''a'' \<noteq>0
         THEN 
         (
          ''add_res'' ::= (A (V ''n'')) 
         )
         ELSE
         (
          ''add_res'' ::= (A (V ''m''))
         ) ;;
        Com.SKIP ;; Com.SKIP ;; Com.SKIP
      )
    )
    ELSE
    (
      ''add_res'' ::= (A (V ''l'')) ;;
      Com.SKIP ;; Com.SKIP ;; Com.SKIP ;;
      Com.SKIP ;; Com.SKIP ;; Com.SKIP ;;
      Com.SKIP ;; Com.SKIP ;; Com.SKIP
    )
  )
  ELSE
  (
    ''add_res'' ::= (A (V ''l'')) ;;
    Com.SKIP ;; Com.SKIP ;; Com.SKIP ;;
    Com.SKIP ;; Com.SKIP ;; Com.SKIP ;;
    Com.SKIP ;; Com.SKIP ;; Com.SKIP ;;
    Com.SKIP ;; Com.SKIP ;; Com.SKIP
  );;
  zero_variables [''a'', ''e'', ''h'', ''k'', ''l'', ''m'', ''n'', ''cons'']"

definition add_res_nat_IMP_Minus where "add_res_nat_IMP_Minus \<equiv>
  add_res_nat_first_part ;;
  add_res_nat_second_part ;;
  add_res_nat_third_part"

definition add_res_nat_IMP_Minus_time where "add_res_nat_IMP_Minus_time n s \<equiv>
  add_res_nat_first_part_time n s
  + add_res_nat_second_part_time n s
  + 15
  + zero_variables_time [''a'', ''e'', ''h'', ''k'', ''l'', ''m'', ''n'', ''cons'']"

lemma add_res_nat_IMP_Minus_correct:
  "(add_res_nat_IMP_Minus, s)
   \<Rightarrow>\<^bsup>add_res_nat_IMP_Minus_time (s ''a'') (s ''b'') \<^esup>
      s(''a'' := 0,
        ''b'' := 0,
        ''c'' := 0,
        ''d'' := 0,
        ''e'' := 0,
        ''f'' := 0,
        ''g'' := 0,
        ''h'' := 0,
        ''i'' := 0,
        ''j'' := 0,
        ''fst_nat'' := 0,
        ''snd_nat'' := 0,
        ''nth_nat'' := 0,
        ''k'' := 0,
        ''l'' := 0,
        ''m'' := 0,
        ''n'' := 0,
        ''cons'' := 0,
        ''triangle'' := 0,
        ''prod_encode'' := 0,
        ''add_res'' := add_res_nat (s ''a'') (s ''b''))"
proof(cases "s ''b''")
  case 0
  show ?thesis
    unfolding add_res_nat_IMP_Minus_def add_res_nat_IMP_Minus_time_def
    apply(rule terminates_in_time_state_intro[OF Seq'
          [OF add_res_nat_second_part_correct]])
    unfolding add_res_nat_third_part_def Let_def add_res_nat_def
    using \<open>s ''b'' = 0\<close> 
    by(fastforce intro: zero_variables_correct)+
next
  case (Suc nat)
  let ?c = "hd_nat (hd_nat (s ''b''))"
  have "?c = 0 \<or> ?c = 1 \<or> ?c = 2 \<or> ?c = 3 \<or> ?c = 4 \<or> ?c = 5 \<or> ?c > 5"
    by auto
  then show ?thesis
    apply(elim disjE)
    unfolding add_res_nat_IMP_Minus_def add_res_nat_IMP_Minus_time_def
    unfolding add_res_nat_third_part_def Let_def add_res_nat_def
    using \<open>s ''b'' = Suc nat\<close>  
          apply simp
    using \<open>s ''b'' = Suc nat\<close>  
    by (fastforce 
         intro!: terminates_in_time_state_intro[OF Seq'[OF 
            add_res_nat_second_part_correct Seq'[OF _ zero_variables_correct]]]
         simp: Let_def)+
qed

definition push_con_first_part where "push_con_first_part \<equiv>
  ''e'' ::= (A (V ''a'')) ;;
  ''f'' ::= (A (V ''b'')) ;;
  
  ''a'' ::= ((V ''a'') \<ominus> (N 1)) ;;
  IMP_Minus_fst_nat ;;
  ''g'' ::= (A (V ''fst_nat'')) ;;
  
  ''a'' ::= (A (N (Suc 0))) ;;
  ''b'' ::= (A (V ''e'')) ;;
  nth_nat_IMP_Minus ;;
  ''h'' ::= (A (V ''nth_nat'')) ;; 

  ''a'' ::= (A (N (Suc (Suc 0)))) ;;
  ''b'' ::= (A (V ''e'')) ;;
  nth_nat_IMP_Minus ;;
  ''i'' ::= (A (V ''nth_nat'')) ;;

  ''a'' ::= (A (N (Suc (Suc (Suc 0))))) ;;
  ''b'' ::= (A (V ''e'')) ;;
  nth_nat_IMP_Minus"

definition push_con_first_part_time where "push_con_first_part_time c s \<equiv>
  (let con = hd_nat c in
    24 + IMP_Minus_fst_nat_time (c - 1) + nth_nat_IMP_Minus_time (Suc 0) c
     + nth_nat_IMP_Minus_time (Suc (Suc 0)) c  
     + nth_nat_IMP_Minus_time (Suc (Suc (Suc 0))) c)"

lemma push_con_first_part_correct:
  "(push_con_first_part, s) \<Rightarrow>\<^bsup>push_con_first_part_time (s ''a'') (s ''b'')\<^esup>
    (let con = hd_nat (s ''a''); 
         e1 = nth_nat (Suc 0) (s ''a'') ; 
         e2 = nth_nat (Suc (Suc 0)) (s ''a''); 
         e3 = nth_nat (Suc (Suc (Suc 0))) (s ''a'') in 
       s(''a'' := 0,
         ''b'' := 0,
         ''c'' := 0,
         ''e'' := s ''a'',
         ''f'' := s ''b'',
         ''g'' := con,
         ''h'' := e1,
         ''i'' := e2,
         ''fst_nat'' := 0,
         ''snd_nat'' := 0,
         ''nth_nat'' := e3))"
  unfolding Let_def push_con_first_part_def push_con_first_part_time_def 
    hd_nat_def
  by (fastforce simp: Let_def intro: terminates_in_time_state_intro[OF Seq] 
      terminates_in_state_intro[OF nth_nat_IMP_Minus_correct]
      IMP_Minus_fst_nat_correct)

definition push_con_second_part where "push_con_second_part \<equiv>
  cons_IMP_Minus (N 0) (N 0) ;;
  ''j'' ::= (A (V ''cons'')) ;;
  
  cons_list_IMP_Minus [N 1, V ''i'', N 0] ;;
  ''k'' ::= (A (V ''cons'')) ;;
    
  cons_list_IMP_Minus [N 2, V ''i'', V ''nth_nat'', N 0] ;;
  ''l'' ::= (A (V ''cons'')) ;;

  cons_list_IMP_Minus [N 5, V ''i'', N 0];; 

  ''nth_nat'' ::= (A (N 0)) ;;
  ''h'' ::= (A (N 0)) ;;
  ''i'' ::= (A (N 0))"

definition push_con_second_part_time where "push_con_second_part_time c s \<equiv>
  (let
    con = hd_nat c;
    e1 = nth_nat (Suc 0) c;
    e2 = nth_nat (Suc (Suc 0)) c;
    e3 = nth_nat (Suc (Suc (Suc 0))) c in
      12 + cons_IMP_Minus_time 0 0
      + cons_list_IMP_Minus_time [1, e2, 0]
      + cons_list_IMP_Minus_time [2, e2, e3, 0]
      + cons_list_IMP_Minus_time [5, e2, 0])"

lemma push_con_second_part_correct:  
  "(push_con_first_part ;; push_con_second_part, s) 
    \<Rightarrow>\<^bsup>push_con_first_part_time (s ''a'') (s ''b'') 
      + push_con_second_part_time (s ''a'') (s ''b'') \<^esup>
    (let con = hd_nat (s ''a'');
         e1 = nth_nat (Suc 0) (s ''a'');
         e2 = nth_nat (Suc (Suc 0)) (s ''a'');
         e3 = nth_nat (Suc (Suc (Suc 0))) (s ''a'');
         l1 = [0, 0];
         l2 = [1, e2, 0];
         l3 = [2, e2, e3, 0];
         l4 = [5, e2, 0]
    in 
      s(''a'' := 0,
        ''b'' := 0,
        ''c'' := 0,
        ''d'' := 0,
        ''e'' := s ''a'',
        ''f'' := s ''b'',
        ''g'' := con,
        ''h'' := 0,
        ''i'' := 0,
        ''fst_nat'' := 0,
        ''snd_nat'' := 0,
        ''nth_nat'' := 0,
        ''j'' := cons_list l1,
        ''k'' := cons_list l2,
        ''l'' := cons_list l3,
        ''cons'' := cons_list l4,
        ''triangle'' := 0,
        ''prod_encode'' := 0))"
  apply(rule terminates_in_state_intro[OF Seq'[OF push_con_first_part_correct]])
  unfolding push_con_second_part_def push_con_second_part_time_def Let_def
  by (fastforce intro: cons_IMP_Minus_correct cons_list_IMP_Minus_correct)+

definition push_con_third_part where "push_con_third_part \<equiv>
  ''a'' ::= ((V ''g'') \<ominus> (N 1)) ;;
  IF ''a'' \<noteq>0 THEN
  (
    ''a'' ::= ((V ''g'') \<ominus> (N 2)) ;;
    IF ''a'' \<noteq>0 THEN
    (
      ''a'' ::= ((V ''g'') \<ominus> (N 3)) ;;
      IF ''a'' \<noteq>0 THEN
      (
        ''a'' ::= (A (V ''cons'')) 
      )
      ELSE
      (
        ''a'' ::= (A (V ''l''))
      )
    )
    ELSE
    (
      Com.SKIP ;; Com.SKIP ;; Com.SKIP ;;
      ''a'' ::= (A (V ''e''))
    )
  )
  ELSE
  (
    Com.SKIP ;; Com.SKIP ;; Com.SKIP ;;
    Com.SKIP ;; Com.SKIP ;;
    IF ''g'' \<noteq>0 THEN
    (
      ''a'' ::= (A (V ''k'')) 
    )
    ELSE
    (
      ''a'' ::= (A (V ''j''))
    )
  ) ;;
  cons_IMP_Minus (V ''a'') (V ''f'') ;;
  ''push_con'' ::= (A (V ''cons'')) ;;
  ''e'' ::= (A (N 0)) ;; 
  ''f'' ::= (A (N 0)) ;;
  ''g'' ::= (A (N 0)) ;; 
  ''j'' ::= (A (N 0)) ;;
  ''k'' ::= (A (N 0)) ;;
  ''l'' ::= (A (N 0)) ;;
  ''cons'' ::= (A (N 0)) ;;
  ''a'' ::= (A (N 0))"

definition push_con_third_part_time where "push_con_third_part_time c s \<equiv>
  (let
    con = hd_nat c;
    e1 = nth_nat (Suc 0) c;
    e2 = nth_nat (Suc (Suc 0)) c;
    e3 = nth_nat (Suc (Suc (Suc 0))) c; 
    l = (
     if con = 0 then (0##0) else 
     if con = 1 then (1##e2##0) else 
     if con = 2 then c else 
     if con = 3 then (2 ## e2 ## e3 ## 0) else
     (5 ## e2 ## 0)) in
      11 + 18 + cons_IMP_Minus_time l s)"

definition push_con_IMP_Minus where "push_con_IMP_Minus \<equiv>
  push_con_first_part ;;
  push_con_second_part ;;
  push_con_third_part"

definition push_con_IMP_Minus_time where "push_con_IMP_Minus_time c s \<equiv>
  push_con_first_part_time c s
  + push_con_second_part_time c s
  + push_con_third_part_time c s"

lemma push_con_IMP_Minus_correct:
  "(push_con_IMP_Minus, s) 
    \<Rightarrow>\<^bsup>push_con_IMP_Minus_time (s ''a'') (s ''b'') \<^esup>
     (s(''a'' := 0,
        ''b'' := 0,
        ''c'' := 0,
        ''d'' := 0,
        ''e'' := 0,
        ''f'' := 0,
        ''g'' := 0,
        ''h'' := 0,
        ''i'' := 0,
        ''fst_nat'' := 0,
        ''snd_nat'' := 0,
        ''nth_nat'' := 0,
        ''j'' := 0,
        ''k'' := 0,
        ''l'' := 0,
        ''cons'' := 0,
        ''triangle'' := 0,
        ''prod_encode'' := 0,
        ''push_con'' := push_con_nat (s ''a'') (s ''b'')))"
proof -
  have "hd_nat (s ''a'') = 0 \<or> hd_nat (s ''a'') = 1 \<or> hd_nat (s ''a'') = 2 
    \<or> hd_nat (s ''a'') = 3 \<or> hd_nat (s ''a'') > 3"
    by auto
  thus ?thesis
    apply(elim disjE)
    unfolding push_con_IMP_Minus_def push_con_IMP_Minus_time_def push_con_nat_def
    by(rule terminates_in_state_intro[OF Seq'
          [OF  push_con_second_part_correct]] ;
        fastforce 
        simp: push_con_third_part_def push_con_third_part_time_def Let_def
        intro: terminates_in_state_intro[OF Seq]
        terminates_in_state_intro[OF Big_StepT.Assign]
        cons_IMP_Minus_correct)+
qed

definition max_constant_iteration_first_part where 
  "max_constant_iteration_first_part \<equiv>
  ''e'' ::= (A (V ''a'')) ;;

  ''a'' ::= ((V ''e'') \<ominus> (N 1)) ;;
  IMP_Minus_fst_nat ;;
  ''f'' ::= (A (V ''fst_nat'')) ;;

  ''a'' ::= ((V ''e'') \<ominus> (N 1)) ;;
  IMP_Minus_snd_nat ;;
  ''g'' ::= (A (V ''snd_nat'')) ;;

  ''a'' ::= ((V ''f'') \<ominus> (N 1)) ;;
  IMP_Minus_fst_nat ;;
  ''h'' ::= (A (V ''fst_nat'')) ;;

  ''a'' ::= (A (N (Suc 0))) ;;
  ''b'' ::= (A (V ''f'')) ;;
  nth_nat_IMP_Minus ;;
  ''i'' ::= (A (V ''nth_nat'')) ;;

  ''a'' ::= (A (N (Suc (Suc 0)))) ;;
  ''b'' ::= (A (V ''f'')) ;;
  nth_nat_IMP_Minus ;;
  ''j'' ::= (A (V ''nth_nat'')) ;;

  ''a'' ::= (A (N (Suc (Suc (Suc 0))))) ;;
  ''b'' ::= (A (V ''f'')) ;;
  nth_nat_IMP_Minus ;;
  ''k'' ::= (A (V ''nth_nat'')) ;;

  ''a'' ::= (A (N (Suc (Suc (Suc (Suc 0)))))) ;;
  ''b'' ::= (A (V ''f'')) ;;
  nth_nat_IMP_Minus ;;
  ''l'' ::= (A (V ''nth_nat''))"

definition max_constant_iteration_first_part_time 
  where "max_constant_iteration_first_part_time s \<equiv>
  (let h = hd_nat s in
    38 + 2 * IMP_Minus_fst_nat_time (s - 1) + IMP_Minus_fst_nat_time (h - 1)
    + nth_nat_IMP_Minus_time (Suc 0) h + nth_nat_IMP_Minus_time (Suc (Suc 0)) h
    + nth_nat_IMP_Minus_time (Suc (Suc (Suc 0))) h
    + nth_nat_IMP_Minus_time (Suc (Suc (Suc (Suc 0)))) h)"

lemma max_constant_iteration_first_part_correct:
  "(max_constant_iteration_first_part, s) 
    \<Rightarrow>\<^bsup>max_constant_iteration_first_part_time (s ''a'')\<^esup>
    (let h = hd_nat (s ''a''); 
         t = tl_nat (s ''a''); 
         c = hd_nat h;  
         e1 = nth_nat (Suc 0) h ; 
         e2 = nth_nat (Suc (Suc 0)) h; 
         e3 = nth_nat (Suc (Suc (Suc 0))) h;
         e4 = nth_nat (Suc (Suc (Suc (Suc 0)))) h in 
       s(''a'' := 0,
         ''b'' := 0,
         ''c'' := 0,
         ''e'' := s ''a'',
         ''f'' := h,
         ''g'' := t,
         ''h'' := c,
         ''i'' := e1,
         ''j'' := e2,
         ''k'' := e3,
         ''l'' := e4,
         ''fst_nat'' := 0,
         ''snd_nat'' := 0,
         ''nth_nat'' := e4))"
  unfolding Let_def max_constant_iteration_first_part_def 
    max_constant_iteration_first_part_time_def hd_nat_def tl_nat_def
  by (fastforce intro: terminates_in_time_state_intro[OF Seq] 
      nth_nat_IMP_Minus_correct
      terminates_in_state_intro[OF Big_StepT.Assign]
      IMP_Minus_fst_nat_correct IMP_Minus_snd_nat_correct)+

(*if c = 0 then  max_constant_stack_nat (add_res_nat 0 t) 
else if c = 1 then max_constant_stack_nat (add_res_nat (aexp_max_constant_tail e1) t)
else if c = 2 then  max_constant_stack_nat (push_con_nat e1 s) 
else if c = 3 then   max_constant_stack_nat (push_con_nat e2 s)
else if c = 4 then   max_constant_stack_nat (add_res_nat (max e3 e4) t)
else if c = 5 then   max_constant_stack_nat (push_con_nat e1 s) 
else if c = 6 then  max_constant_stack_nat (add_res_nat e2 t)
else e1*)

definition max_constant_iteration_second_part where "max_constant_iteration_second_part \<equiv>
  ''max_constant'' ::= (A (N 1)) ;;
  IF ''e'' \<noteq>0 THEN
    IF ''h'' \<noteq>0 THEN
    (
      ''a'' ::= ((V ''h'') \<ominus> (N 1)) ;;
      IF ''a'' \<noteq>0 THEN
      (
        ''a'' ::= ((V ''h'') \<ominus> (N 2)) ;;
        IF ''a'' \<noteq>0 THEN
        (
          ''a'' ::= ((V ''h'') \<ominus> (N 3)) ;;
          IF ''a'' \<noteq>0 THEN
          (
            ''a'' ::= ((V ''h'') \<ominus> (N 4)) ;;
            IF ''a'' \<noteq>0 THEN
            (
              ''a'' ::= ((V ''h'') \<ominus> (N 5)) ;;
              IF ''a'' \<noteq>0 THEN
              (
                ''a'' ::= ((V ''h'') \<ominus> (N 6)) ;;
                IF ''a'' \<noteq>0 THEN
                (
                  ''a'' ::= (A (V ''i'')) ;;
                  ''max_constant'' ::= (A (N 0))
                )
                ELSE
                (
                  ''a'' ::= (A (V ''j'')) ;;
                  ''b'' ::= (A (V ''g'')) ;;
                  add_res_nat_IMP_Minus ;;
                  ''a'' ::= (A (V ''add_res''))
                )
              )
              ELSE
              (
                ''a'' ::= (A (V ''i'')) ;;
                ''b'' ::= (A (V ''e'')) ;;
                push_con_IMP_Minus ;;
                ''a'' ::= (A (V ''push_con''))
              )
            )
            ELSE
            (
              ''a'' ::= (A (V ''k'')) ;;
              ''b'' ::= (A (V ''l'')) ;;
              IMP_Minus_max_a_min_b ;;
              ''b'' ::= (A (V ''g'')) ;;
              add_res_nat_IMP_Minus ;;
              ''a'' ::= (A (V ''add_res''))
            )
          )
          ELSE
          (
            ''a'' ::= (A (V ''j'')) ;;
            ''b'' ::= (A (V ''e'')) ;;
            push_con_IMP_Minus ;;
            ''a'' ::= (A (V ''push_con''))
          )
        )
        ELSE
        (
          ''a'' ::= (A (V ''i'')) ;;
          ''b'' ::= (A (V ''e'')) ;;
          push_con_IMP_Minus ;;
          ''a'' ::= (A (V ''push_con''))
        )
      )
      ELSE
      (
        ''a'' ::= (A (V ''i'')) ;;
        aexp_max_constant_IMP_Minus ;;
        ''a'' ::= (A (V ''aexp_max_constant'')) ;;
        ''b'' ::= (A (V ''g'')) ;;
        add_res_nat_IMP_Minus ;;
        ''a'' ::= (A (V ''add_res''))
      )
    )
    ELSE
    (
      ''a'' ::= (A (N 0)) ;;
      ''b'' ::= (A (V ''g'')) ;;
      add_res_nat_IMP_Minus ;;
      ''a'' ::= (A (V ''add_res''))
    )
  ELSE
  (
    ''a'' ::= (A (N 0)) ;;
    ''max_constant'' ::= (A (N 0))
  ) ;;
  zero_variables [''d'', ''e'', ''f'', ''g'', ''h'', ''i'', ''j'', ''k'', ''l'', ''m'', ''n'',
    ''nth_nat'', ''aexp_max_constant'', ''add_res'', ''cons'', ''triangle'',
        ''prod_encode'', ''add_res'', ''atomExp_to_constant'', ''push_con'']"

definition max_constant_iteration_second_part_time where 
  "max_constant_iteration_second_part_time s \<equiv>
  Suc (Suc 0) + 
  (let h = hd_nat s; 
       t = tl_nat s; 
       c = hd_nat h;  
       e1 = nth_nat (Suc 0) h ; 
       e2 = nth_nat (Suc (Suc 0)) h; 
       e3 = nth_nat (Suc (Suc (Suc 0))) h;
       e4 = nth_nat (Suc (Suc (Suc (Suc 0)))) h in 
      (if s = 0 then 1 + 4 
       else 1 + 
       (if c = 0 then 1 + 6 + (add_res_nat_IMP_Minus_time 0 t) 
       else if c = 1 then 4 + 8 
          + (add_res_nat_IMP_Minus_time (aexp_max_constant_tail e1) t)
          + (aexp_max_constant_IMP_Minus_time e1)
       else if c = 2 then 7 + 6 + (push_con_IMP_Minus_time e1 s) 
       else if c = 3 then 10 + 6 + (push_con_IMP_Minus_time e2 s)
       else if c = 4 then 13 + 8 + 11 + (add_res_nat_IMP_Minus_time (max e3 e4) t)
       else if c = 5 then 16 + 6 + (push_con_IMP_Minus_time e1 s) 
       else if c = 6 then 19 + 6 + (add_res_nat_IMP_Minus_time e2 t)
       else 19 + 4)))
  + zero_variables_time [''d'', ''e'', ''f'', ''g'', ''h'', ''i'', ''j'', ''k'', ''l'', ''m'', ''n'',
    ''nth_nat'', ''aexp_max_constant'', ''add_res'', ''cons'', ''triangle'',
        ''prod_encode'', ''add_res'', ''atomExp_to_constant'', ''push_con'']"

definition max_constant_iteration where "max_constant_iteration \<equiv>
  max_constant_iteration_first_part ;;
  max_constant_iteration_second_part"

definition max_constant_iteration_time where "max_constant_iteration_time s \<equiv>
  max_constant_iteration_first_part_time s 
  + max_constant_iteration_second_part_time s"

lemma max_constant_iteration_correct: 
"(max_constant_iteration, s') 
    \<Rightarrow>\<^bsup>max_constant_iteration_time (s' ''a'')\<^esup>
    (let s = s' ''a'';
         h = hd_nat s; 
         t = tl_nat s; 
         c = hd_nat h;  
         e1 = nth_nat (Suc 0) h ; 
         e2 = nth_nat (Suc (Suc 0)) h; 
         e3 = nth_nat (Suc (Suc (Suc 0))) h;
         e4 = nth_nat (Suc (Suc (Suc (Suc 0)))) h in 
       s'(''a'' := 
          (if s = 0 then 0
           else (if c = 0 then (add_res_nat 0 t) 
           else if c = 1 then (add_res_nat (aexp_max_constant_tail e1) t)
           else if c = 2 then (push_con_nat e1 s) 
           else if c = 3 then (push_con_nat e2 s)
           else if c = 4 then (add_res_nat (max e3 e4) t)
           else if c = 5 then (push_con_nat e1 s) 
           else if c = 6 then (add_res_nat e2 t)
           else e1)),
         ''b'' := 0,
         ''c'' := 0,
         ''d'' := 0,
         ''e'' := 0,
         ''f'' := 0,
         ''g'' := 0,
         ''h'' := 0,
         ''i'' := 0,
         ''j'' := 0,
         ''k'' := 0,
         ''l'' := 0,
         ''m'' := 0,
         ''n'' := 0,
         ''max_constant'' := (if s \<noteq> 0 \<and> c < 7 then 1 else 0),
         ''fst_nat'' := 0,
         ''snd_nat'' := 0,
         ''nth_nat'' := 0,
         ''cons'' := 0,
         ''triangle'' := 0,
         ''prod_encode'' := 0,
         ''aexp_max_constant'' := 0,
         ''atomExp_to_constant'' := 0,
         ''add_res'' := 0,
         ''push_con'' := 0))"
proof (cases "s' ''a''")
  case 0
  then show ?thesis
     unfolding max_constant_iteration_def max_constant_iteration_time_def
      max_constant_iteration_second_part_def max_constant_iteration_second_part_time_def
    by(fastforce 
        simp: Let_def 
        intro: 
          aexp_max_constant_IMP_Minus_correct IMP_Minus_max_a_min_b_correct
          add_res_nat_IMP_Minus_correct push_con_IMP_Minus_correct
        intro!: 
          terminates_in_state_intro[OF Seq'
          [OF max_constant_iteration_first_part_correct
            Seq'[OF Seq'[OF Big_StepT.Assign] zero_variables_correct]]])
next
  case (Suc nat)

  let ?c = "hd_nat (hd_nat (s' ''a''))"
  have "?c = 0 \<or> ?c = 1 \<or> ?c = 2 \<or> ?c = 3 \<or> ?c = 4 \<or> ?c = 5 \<or> ?c = 6 \<or> ?c > 6"
    by auto
  thus ?thesis
    unfolding max_constant_iteration_def max_constant_iteration_time_def
      max_constant_iteration_second_part_def max_constant_iteration_second_part_time_def
    apply(elim disjE)
    using Suc
    by(fastforce 
        simp: Let_def 
        intro: 
          aexp_max_constant_IMP_Minus_correct IMP_Minus_max_a_min_b_correct
          add_res_nat_IMP_Minus_correct push_con_IMP_Minus_correct
        intro!: 
          terminates_in_state_intro[OF Seq'
          [OF max_constant_iteration_first_part_correct
            Seq'[OF Seq'[OF Big_StepT.Assign] zero_variables_correct]]])+
qed

function (domintros) max_constant_loop_time :: "nat \<Rightarrow> nat" where
"max_constant_loop_time s = 
  1 + max_constant_iteration_time s + 
  (if s = 0 then 2 
   else (let h = hd_nat s;
         t = tl_nat s;
         c = hd_nat h;
         e1 = nth_nat (Suc 0) h;
         e2 = nth_nat (Suc (Suc 0)) h;
         e3 = nth_nat (Suc (Suc (Suc 0))) h;
         e4 = nth_nat (Suc (Suc (Suc (Suc 0)))) h in 
      if c = 0 then max_constant_loop_time (add_res_nat 0 t) 
      else if c = 1 then max_constant_loop_time (add_res_nat (aexp_max_constant_tail e1) t)
      else if c = 2 then max_constant_loop_time (push_con_nat e1 s) 
      else if c = 3 then max_constant_loop_time (push_con_nat e2 s)
      else if c = 4 then max_constant_loop_time (add_res_nat (max e3 e4) t)
      else if c = 5 then max_constant_loop_time (push_con_nat e1 s) 
      else if c = 6 then max_constant_loop_time (add_res_nat e2 t)
      else 2))"
  by pat_completeness auto

lemma max_constant_stack_nat_domain_then_max_constant_loop_time_domain:
  "max_constant_stack_nat_dom x \<Longrightarrow> max_constant_loop_time_dom x"
proof(induction x rule: max_constant_stack_nat.pinduct)
  case (1 s)

  show ?case 
  proof (cases s)
    case 0
    then show ?thesis
      using max_constant_loop_time.domintros[where ?s=s]
      by auto
  next
    case (Suc nat)
    show ?thesis
      by(fastforce intro: 
          max_constant_loop_time.domintros[where ?s=s]
          "1.IH"[where ?x="hd_nat s", simplified])
  qed
qed

lemma max_constant_loop_correct:
   "max_constant_stack_nat_dom s \<Longrightarrow> s' ''a'' = s \<Longrightarrow> 
    0 < s' ''max_constant'' \<Longrightarrow>
(WHILE ''max_constant''\<noteq>0 DO max_constant_iteration, s') 
    \<Rightarrow>\<^bsup>max_constant_loop_time s\<^esup>
      s'(''a'' := max_constant_stack_nat s,
         ''b'' := 0,
         ''c'' := 0,
         ''d'' := 0,
         ''e'' := 0,
         ''f'' := 0,
         ''g'' := 0,
         ''h'' := 0,
         ''i'' := 0,
         ''j'' := 0,
         ''k'' := 0,
         ''l'' := 0,
         ''m'' := 0,
         ''n'' := 0,
         ''max_constant'' := 0,
         ''fst_nat'' := 0,
         ''snd_nat'' := 0,
         ''nth_nat'' := 0,
         ''cons'' := 0,
         ''triangle'' := 0,
         ''prod_encode'' := 0,
         ''aexp_max_constant'' := 0,
         ''atomExp_to_constant'' := 0,
         ''add_res'' := 0,
         ''push_con'' := 0)"
proof(induction s arbitrary: s' rule: max_constant_stack_nat.pinduct)
  case (1 s)
  
  let ?c = "hd_nat (hd_nat s)"

  show ?case
  proof (cases "s \<noteq> 0 \<and> ?c < 7")
    case True

    hence "?c = 0 \<or> ?c = 1 \<or> ?c = 2 \<or> ?c = 3 \<or> ?c = 4 \<or> ?c = 5 \<or> ?c = 6" 
      by auto

    then show ?thesis
      apply(elim disjE)
      using \<open>0 < s' ''max_constant''\<close>
        \<open>s \<noteq> 0 \<and> hd_nat (hd_nat s) < 7\<close> \<open>s' ''a'' = s\<close>
        max_constant_loop_time.psimps
        max_constant_stack_nat.psimps
        max_constant_stack_nat_domain_then_max_constant_loop_time_domain
        \<open>max_constant_stack_nat_dom s\<close>
            apply -
            apply (fastforce
              simp: Let_def
              intro!: 
                terminates_in_state_intro
                [OF Big_StepT.WhileTrue[OF _ max_constant_iteration_correct "1.IH"(1)]])
           apply (fastforce
              simp: Let_def
              intro!: 
                terminates_in_state_intro
                [OF Big_StepT.WhileTrue[OF _ max_constant_iteration_correct "1.IH"(2)]])
          apply (fastforce
            simp: Let_def
            intro!: 
            terminates_in_state_intro
            [OF Big_StepT.WhileTrue[OF _ max_constant_iteration_correct "1.IH"(3)]])
         apply (fastforce
          simp: Let_def
          intro!: 
          terminates_in_state_intro
          [OF Big_StepT.WhileTrue[OF _ max_constant_iteration_correct "1.IH"(4)]])
        apply (fastforce
          simp: Let_def
          intro!: 
          terminates_in_state_intro
          [OF Big_StepT.WhileTrue[OF _ max_constant_iteration_correct "1.IH"(5)]])
       apply (fastforce
          simp: Let_def
          intro!: 
          terminates_in_state_intro
          [OF Big_StepT.WhileTrue[OF _ max_constant_iteration_correct "1.IH"(6)]])
      by (fastforce
          simp: Let_def
          intro!: 
          terminates_in_state_intro
          [OF Big_StepT.WhileTrue[OF _ max_constant_iteration_correct "1.IH"(7)]])
  next
    case False

    show ?thesis
    proof(cases s)
      case 0
      thus ?thesis
        using 
          \<open>0 < s' ''max_constant''\<close>
          max_constant_loop_time.psimps[OF max_constant_loop_time.domintros]
          max_constant_stack_nat.psimps[OF max_constant_stack_nat.domintros]
          \<open>s' ''a'' = s\<close>
        by (auto intro!: terminates_in_state_intro[OF Big_StepT.WhileTrue
              [OF _ max_constant_iteration_correct Big_StepT.WhileFalse]])
    next
      case (Suc nat)
      hence "s \<noteq> 0" "?c > 6"
        using \<open>\<not> (s \<noteq> 0 \<and> ?c < 7)\<close>
        by auto
      thus ?thesis
        using 
          \<open>0 < s' ''max_constant''\<close>
          max_constant_loop_time.psimps[OF max_constant_loop_time.domintros]
          max_constant_stack_nat.psimps[OF max_constant_stack_nat.domintros]
          \<open>s' ''a'' = s\<close>
        by (auto intro!: terminates_in_state_intro[OF Big_StepT.WhileTrue
              [OF _ max_constant_iteration_correct Big_StepT.WhileFalse]])
    qed
  qed
qed

definition max_constant_IMP_Minus where "max_constant_IMP_Minus \<equiv>
  ''max_constant'' ::= (A (N 1)) ;;
  WHILE ''max_constant''\<noteq>0 DO max_constant_iteration ;;
  ''max_constant'' ::= (A (V ''a'')) ;;
  ''a'' ::= (A (N 0))" 

definition max_constant_time where "max_constant_time s \<equiv>
  6 + max_constant_loop_time s" 

lemma max_constant_IMP_Minus_correct: 
"max_constant_stack_nat_dom (s ''a'') \<Longrightarrow> 
    0 < s' ''max_constant'' \<Longrightarrow>
(max_constant_IMP_Minus, s) 
    \<Rightarrow>\<^bsup>max_constant_time (s ''a'')\<^esup>
       s(''a'' := 0,
         ''b'' := 0,
         ''c'' := 0,
         ''d'' := 0,
         ''e'' := 0,
         ''f'' := 0,
         ''g'' := 0,
         ''h'' := 0,
         ''i'' := 0,
         ''j'' := 0,
         ''k'' := 0,
         ''l'' := 0,
         ''m'' := 0,
         ''n'' := 0,
         ''max_constant'' := max_constant_stack_nat (s ''a''),
         ''fst_nat'' := 0,
         ''snd_nat'' := 0,
         ''nth_nat'' := 0,
         ''cons'' := 0,
         ''triangle'' := 0,
         ''prod_encode'' := 0,
         ''aexp_max_constant'' := 0,
         ''atomExp_to_constant'' := 0,
         ''add_res'' := 0,
         ''push_con'' := 0)"
  unfolding max_constant_IMP_Minus_def max_constant_time_def 
  by(fastforce intro!: terminates_in_state_intro[OF Seq] max_constant_loop_correct)

end 