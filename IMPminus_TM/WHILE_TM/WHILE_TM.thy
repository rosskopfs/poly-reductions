theory WHILE_TM
  imports "IMP_Minus.AExp" "IMP_Minus.Com" "HOL-IMP.Star" Main  "IMP_Minus.Big_StepT"
   Cook_Levin.Basics Cook_Levin.Combinations
begin

fun count_atomExp_variable ::"atomExp \<Rightarrow>vname set" where
"count_atomExp_variable (N val) ={}"| 
"count_atomExp_variable (V vname) ={vname}"

fun count_aexp_variable::"aexp \<Rightarrow>vname set" where
"count_aexp_variable (A a) =count_atomExp_variable a "|
"count_aexp_variable  (Plus a b)=(count_atomExp_variable a)\<union>(count_atomExp_variable b)" |
"count_aexp_variable  (Sub a b)=(count_atomExp_variable a)\<union>(count_atomExp_variable b)" |
"count_aexp_variable (Parity a) =count_atomExp_variable a "|
"count_aexp_variable  (RightShift a) =count_atomExp_variable a "              

fun count_com_variable::"com \<Rightarrow>vname set" where
"count_com_variable  SKIP ={}"|
"count_com_variable (Assign vname a) ={vname}\<union> (count_aexp_variable a)"|
"count_com_variable (Seq Seq1 Seq2)=(count_com_variable Seq1)\<union> (count_com_variable Seq2)"|
"count_com_variable (If vname com1 com2) = {vname}\<union> (count_com_variable com1)\<union> (count_com_variable com2)"|
"count_com_variable (While  vname com1) = {vname}\<union> (count_com_variable com1)"

(*
instantiation char :: linorder begin
fun less_eq_char where "(l1::char) \<le> l2 \<longleftrightarrow> True"
fun less_char where "(l1::char) < l2 \<longleftrightarrow> True"
instance sorry
end

instantiation list :: (linorder) linorder begin
fun less_eq_list where "(l1::('a::linorder) list) \<le> l2 \<longleftrightarrow> True"
fun less_list where "(l1::('a::linorder) list) < l2 \<longleftrightarrow> True"
instance sorry
end

fun vars_to_nat:: "com \<Rightarrow> vname \<Rightarrow> nat" where
"vars_to_nat prog x = list (count_com_variable prog)"

value "sorted_list_of_set {''a'', ''n''}"
*)

(*
definition turing_machine :: "nat \<Rightarrow> nat \<Rightarrow> machine \<Rightarrow> bool" where
  "turing_machine k G M \<equiv> k \<ge> 2 \<and> G \<ge> 4 \<and> (\<forall>cmd\<in>set M. turing_command k (length M) G cmd)"
*)

(*TODO : numbering every variable from 1*) 
fun num_variable::" com \<Rightarrow> (vname \<Rightarrow> nat)" where
"num_variable com  =(\<lambda>s. 1)"

fun update_list::"nat \<Rightarrow>'a \<Rightarrow>'a list \<Rightarrow>'a list" where 
"update_list _ _ [] =[]"|
"update_list 0 new_ele (x#xs) =new_ele#xs"|
"update_list (Suc n) new_ele (x#xs) =x#(update_list n new_ele xs)"

fun write_bit_tape::"nat \<Rightarrow>nat \<Rightarrow>command" where
"write_bit_tape b k=( \<lambda> symbols_read_from_tapes.
      (
        1, \<comment> \<open>new state\<close>
        let len =(length symbols_read_from_tapes);
         new_symbols_of_tapes =(update_list k (b+2) symbols_read_from_tapes);
        directions = (replicate  (k-1) Stay)@ [Right]@(replicate  (len-k) Stay)
          in
       (zip new_symbols_of_tapes  directions)
      )
   )"

(*
definition wf_command :: "nat \<Rightarrow> nat \<Rightarrow> command \<Rightarrow> bool" where
  "wf_command k Q cmd \<equiv> \<forall>gs. length gs = k \<longrightarrow> length (snd (cmd gs)) = k \<and> fst (cmd gs) \<le> Q"
*)


fun write_end_tape::"nat \<Rightarrow>command" where
"write_end_tape k=( \<lambda> symbols_read_from_tapes.
      (
        2, \<comment> \<open>new state\<close>
        let len =(length symbols_read_from_tapes);
         new_symbols_of_tapes =(update_list k 0 symbols_read_from_tapes);
        directions = (replicate  (k-1) Stay)@ [Left]@(replicate  (len-k) Stay)
          in
       (zip new_symbols_of_tapes  directions)
      )
   )"

lemma write_end_tape_wf_command:
  (* there are K tapes in total, and we write a number n to kth tape*)
  fixes n k K G
  assumes "k\<ge>1" and "K\<ge>k" and "Q\<ge>4"
  shows "wf_command K Q (write_end_tape k)"
fun count_atomExp_variable ::"atomExp \<Rightarrow>vname set" where
"count_atomExp_variable (N val) ={}"| 
"count_atomExp_variable (V vname) ={vname}"

fun count_aexp_variable::"aexp \<Rightarrow>vname set" where
"count_aexp_variable (A a) =count_atomExp_variable a "|
"count_aexp_variable  (Plus a b)=(count_atomExp_variable a)\<union>(count_atomExp_variable b)" |
"count_aexp_variable  (Sub a b)=(count_atomExp_variable a)\<union>(count_atomExp_variable b)" |
"count_aexp_variable (Parity a) =count_atomExp_variable a "|
"count_aexp_variable  (RightShift a) =count_atomExp_variable a "              

fun count_com_variable::"com \<Rightarrow>vname set" where
"count_com_variable  SKIP ={}"|
"count_com_variable (Assign vname a) ={vname}\<union> (count_aexp_variable a)"|
"count_com_variable (Seq Seq1 Seq2)=(count_com_variable Seq1)\<union> (count_com_variable Seq2)"|
"count_com_variable (If vname com1 com2) = {vname}\<union> (count_com_variable com1)\<union> (count_com_variable com2)"|
"count_com_variable (While  vname com1) = {vname}\<union> (count_com_variable com1)"

(*
instantiation char :: linorder begin
fun less_eq_char where "(l1::char) \<le> l2 \<longleftrightarrow> True"
fun less_char where "(l1::char) < l2 \<longleftrightarrow> True"
instance sorry
end

instantiation list :: (linorder) linorder begin
fun less_eq_list where "(l1::('a::linorder) list) \<le> l2 \<longleftrightarrow> True"
fun less_list where "(l1::('a::linorder) list) < l2 \<longleftrightarrow> True"
instance sorry
end

fun vars_to_nat:: "com \<Rightarrow> vname \<Rightarrow> nat" where
"vars_to_nat prog x = list (count_com_variable prog)"

value "sorted_list_of_set {''a'', ''n''}"
*)

(*
definition turing_machine :: "nat \<Rightarrow> nat \<Rightarrow> machine \<Rightarrow> bool" where
  "turing_machine k G M \<equiv> k \<ge> 2 \<and> G \<ge> 4 \<and> (\<forall>cmd\<in>set M. turing_command k (length M) G cmd)"
*)

(*TODO : numbering every variable from 1*) 
fun num_variable::" com \<Rightarrow> (vname \<Rightarrow> nat)" where
"num_variable com  =(\<lambda>s. 1)"

fun update_list::"nat \<Rightarrow>'a \<Rightarrow>'a list \<Rightarrow>'a list" where 
"update_list _ _ [] =[]"|
"update_list 0 new_ele (x#xs) =new_ele#xs"|
"update_list (Suc n) new_ele (x#xs) =x#(update_list n new_ele xs)"

lemma length_update_list:"length ( update_list n a l) =length l"
  apply (induction  l arbitrary:n a  )
   apply simp
  by (smt (verit) length_Cons list.sel(3) update_list.elims)

lemma l1:"k\<ge>1\<and>k\<le>length gs \<longrightarrow>length ((replicate (k - 1) Stay) @ [Left] @ (replicate (length gs - k) Stay)) = length gs"
  apply simp
  by auto
lemma length_replicate:"length ( replicate n a ) =n"
  by simp
fun write_bit_tape::"nat \<Rightarrow>nat \<Rightarrow>command" where
"write_bit_tape b k=( \<lambda> symbols_read_from_tapes.
      (
        0, \<comment> \<open>new state\<close>
        let len =(length symbols_read_from_tapes);
         new_symbols_of_tapes =(update_list k (b+2) symbols_read_from_tapes);
        directions = (replicate  (k-1) Stay)@ [Right]@(replicate  (len-k) Stay)
          in
       (zip new_symbols_of_tapes  directions)
      )
   )"

(*
definition wf_command :: "nat \<Rightarrow> nat \<Rightarrow> command \<Rightarrow> bool" where
  "wf_command k Q cmd \<equiv> \<forall>gs. length gs = k \<longrightarrow> length (snd (cmd gs)) = k \<and> fst (cmd gs) \<le> Q"
*)


fun write_end_tape::"nat \<Rightarrow>command" where
"write_end_tape k=( \<lambda> symbols_read_from_tapes.
      (
        1, \<comment> \<open>new state\<close>
        let len =(length symbols_read_from_tapes);
         new_symbols_of_tapes =(update_list k 0 symbols_read_from_tapes);
        directions = (replicate  (k-1) Stay)@ [Left]@(replicate  (len-k) Stay)
          in
       (zip new_symbols_of_tapes  directions)
      )
   )"

lemma write_end_tape_wf_command:
  fixes k K Q
  assumes "k \<ge> 1" and "K \<ge> k" and "Q \<ge> 4"
  shows "wf_command K Q (write_end_tape k)"
  using assms
proof -
  have x:"wf_command K Q (write_end_tape k) \<longleftrightarrow> (\<forall>gs. length gs = K \<longrightarrow> length (snd (write_end_tape k gs)) = K \<and> fst (write_end_tape k gs) \<le> Q)"
    by (simp add: wf_command_def)
  show "wf_command K Q (write_end_tape k)"
  proof (subst wf_command_def, rule allI, rule impI)
    fix gs :: "nat list"
    assume "length gs = K"
    have "write_end_tape k gs = (
      let len = length gs;
          new_symbols_of_tapes = update_list k 0 gs;
          directions = (replicate (k - 1) Stay) @ [Left] @ (replicate (len - k) Stay)
      in (2, (zip new_symbols_of_tapes directions))
    )"
      by (simp add: write_end_tape.simps)
    then have cmd_def: "write_end_tape k gs = (
      let len = length gs;
          new_symbols_of_tapes = update_list k 0 gs;
          directions = (replicate (k - 1) Stay) @ [Left] @ (replicate (len - k) Stay)
      in (2, (zip new_symbols_of_tapes directions))
    )"
      by simp
    (* Check the length of the resulting symbols *)
    have "length (snd (write_end_tape k gs)) = length (zip (update_list k 0 gs) ((replicate (k - 1) Stay) @ [Left] @ (replicate (length gs - k) Stay)))"
      by (simp add: cmd_def)
    moreover have "length (update_list k 0 gs) = length gs"
    by (simp add: length_update_list)
    moreover have "length ((replicate (k - 1) Stay) @ [Left] @ (replicate (length gs - k) Stay)) = length gs"
    using \<open>length gs = K\<close> assms(1) assms(2) l1 by blast
    ultimately have "length (snd (write_end_tape k gs)) = K"
      by (simp add: \<open>length gs = K\<close>)
    (* Check the state *)
    have "fst (write_end_tape k gs) = 2"
      by (simp add: cmd_def)
    then have "fst (write_end_tape k gs) \<le> Q"
      using \<open>Q \<ge> 4\<close> by simp
    (* Combine the results *)
    show "length (snd (write_end_tape k gs)) = K \<and> fst (write_end_tape k gs) \<le> Q"
    using \<open>[*] write_end_tape k gs \<le> Q\<close> \<open>length ([!!] write_end_tape k gs) = K\<close> by blast
      (*by (simp add: \<open>length (snd (write_end_tape k gs)) = K\<close> \<open>fst (write_end_tape k gs) \<le> Q\<close>)*)
  qed
qed



lemma write_end_tape_wf_command:
  fixes k K Q
  assumes "k \<ge> 1" and "K \<ge> k" and "Q \<ge> 4"
  shows "wf_command K Q (write_end_tape k)"
  using assms
  sorry



fun one_tape_back_start::"nat\<Rightarrow> command" where
"one_tape_back_start k=( \<lambda> symbols_read_from_tapes.
      (
        3, \<comment> \<open>new state\<close>
        if symbols_read_from_tapes!0 = 0 then 
        let len =(length symbols_read_from_tapes);
        directions = (replicate  (k-1) Stay)@ [Right]@(replicate  (len-k) Stay)
          in
       (zip symbols_read_from_tapes  directions)
      else 
        let len =(length symbols_read_from_tapes);
        directions = (replicate  (k-1) Stay)@ [Left]@(replicate  (len-k) Stay)
          in
       (zip symbols_read_from_tapes  directions)
      )
)"

(*
abbreviation (input) blank_symbol :: nat ("\<box>") where "\<box> \<equiv> 0"
abbreviation (input) start_symbol :: nat ("\<triangleright>")   where "\<triangleright> \<equiv> 1"
abbreviation (input) zero_symbol :: nat ("\<zero>")   where "\<zero> \<equiv> 2"
abbreviation (input) one_symbol :: nat ("\<one>")    where "\<one> \<equiv> 3"
abbreviation (input) bar_symbol :: nat ("\<bar>")      where "\<bar> \<equiv> 4"
abbreviation (input) sharp_symbol :: nat ("\<sharp>")  where "\<sharp> \<equiv> 5"
*)


fun write_nat_tape::"nat \<Rightarrow>nat \<Rightarrow> machine" where
" write_nat_tape 0 k = [write_end_tape k,one_tape_back_start k]"|
" write_nat_tape n k =  (
   (write_bit_tape (n mod 2) k)# (write_nat_tape (n div 2 ) k)
   )"

(*
definition wf_command :: "nat \<Rightarrow> nat \<Rightarrow> command \<Rightarrow> bool" where
  "wf_command k Q cmd \<equiv> \<forall>gs. length gs = k \<longrightarrow> length (snd (cmd gs)) = k \<and> fst (cmd gs) \<le> Q"
*)



theorem write_nat_maschine:
  (* there are K tapes in total, and we write a number n to kth tape*)
  fixes n k K G
  assumes "k\<ge>1" and "K\<ge>k+1" and "G\<ge>4"
  shows "turing_machine K G (write_nat_tape n k)  "
  using assms 
 proof (induction n)
  case 0
  then show ?case
  proof -
    have "K \<ge> 2" using assms(2) assms(1) by linarith
    moreover have "G \<ge> 4" using assms(3) by simp
    moreover have "(\<forall>cmd\<in>set (write_nat_tape 0 k). turing_command K (length (write_nat_tape 0 k)) G cmd)"
    proof
      fix cmd
      assume "cmd \<in> set (write_nat_tape 0 k)"
      then have "cmd = write_end_tape k \<or> cmd = one_tape_back_start k" 
        by (simp add: write_nat_tape.simps)
      then show "turing_command K (length (write_nat_tape 0 k)) G cmd"
      proof
        assume "cmd = write_end_tape k"
        (* Assuming write_end_tape is a valid turing command *)
        then have "wf_command K G cmd" 
          by (meson add_leD1 assms(1) assms(2) calculation(2) write_end_tape_wf_command)
        have "(\<forall>gs. length gs = k \<longrightarrow>
      ((\<forall>i<k. gs ! i < G) \<longrightarrow> (\<forall>i<k. fst (snd (cmd gs) ! i) < G)) \<and>
       (k > 0 \<longrightarrow> fst (snd (cmd gs) ! 0) = gs ! 0))"
        proof -
           fix gs
           assume "length gs = k"
         qed
      then show "turing_command K (length (write_nat_tape 0 k)) G cmd"
          by (simp add: turing_command_def wf_command_def) (* 需要假设 write_end_tape 满足 turing_command *)
      next
        assume "cmd = one_tape_back_start k"
        (* Assuming one_tape_back_start is a valid turing command *)
        then show "turing_command K (length (write_nat_tape 0 k)) G cmd"
          by (simp add: turing_command_def wf_command_def) (* 需要假设 one_tape_back_start 满足 turing_command *)
      qed
    qed
    ultimately show "turing_machine K G (write_nat_tape 0 k)"
      by (simp add: turing_machine_def)
  qed
next
  case (Suc n)
  then show ?case
  proof -
    have "K \<ge> 2" using assms(2) by simp
    moreover have "G \<ge> 4" using assms(3) by simp
    moreover have "(\<forall>cmd\<in>set (write_nat_tape (Suc n) k). turing_command K (length (write_nat_tape (Suc n) k)) G cmd)"
    proof
      fix cmd
      assume "cmd \<in> set (write_nat_tape (Suc n) k)"
      then have "cmd = write_bit_tape ((Suc n) mod 2) k \<or> cmd \<in> set (write_nat_tape (Suc n div 2) k)"
        by (simp add: write_nat_tape.simps)
      then show "turing_command K (length (write_nat_tape (Suc n) k)) G cmd"
      proof
        assume "cmd = write_bit_tape ((Suc n) mod 2) k"
        (* Assuming write_bit_tape is a valid turing command *)
        then show "turing_command K (length (write_nat_tape (Suc n) k)) G cmd"
          by (simp add: turing_command_def wf_command_def) (* 需要假设 write_bit_tape 满足 turing_command *)
      next
        assume "cmd \<in> set (write_nat_tape (Suc n div 2) k)"
        then show "turing_command K (length (write_nat_tape (Suc n) k)) G cmd"
          using Suc.IH assms(1) assms(2) assms(3) by simp
      qed
    qed
    ultimately show "turing_machine K G (write_nat_tape (Suc n) k)"
      by (simp add: turing_machine_def)
  qed
qed




definition stay_direction ::"nat\<Rightarrow>direction list" where
" stay_direction n=replicate  n Stay"

definition two_tapes_move_right :: "nat \<Rightarrow>nat\<Rightarrow>nat\<Rightarrow>direction list" where
  "two_tapes_move_right k1 k2 n=(update_list k1 Right(update_list k2 Right (stay_direction n)))"

definition two_tapes_move_left :: "nat \<Rightarrow>nat\<Rightarrow>nat\<Rightarrow>direction list" where
  "two_tapes_move_left k1 k2 n=(update_list k1 Left(update_list k2 Left (stay_direction n)))"

 \<comment> \<open>copy k2 to k1\<close>
fun copy_tape::" nat\<Rightarrow>nat \<Rightarrow>command" where
"copy_tape k1 k2 =(\<lambda> symbols_read_from_tapes.
      (
       if symbols_read_from_tapes!k2 = 0 then 5 else 4
        , \<comment> \<open>new state\<close>
        if symbols_read_from_tapes!k2 = 0 then 
        let 
          len =(length symbols_read_from_tapes);
          new_symbol_tape=(update_list k1 0 symbols_read_from_tapes);
          directions =(two_tapes_move_left k1 k2 len)
          in
       (zip symbols_read_from_tapes  directions)
      else 
        let 
            len =(length symbols_read_from_tapes);
           new_symbol_tape=(update_list k1 (symbols_read_from_tapes!k2) symbols_read_from_tapes);
        directions = (two_tapes_move_right k1 k2 len)
          in
       (zip symbols_read_from_tapes  directions)
      )
)"

fun two_tape_back_start::"nat\<Rightarrow>nat\<Rightarrow> command" where
"two_tape_back_start k1 k2=( \<lambda> symbols_read_from_tapes.
      (
        6, \<comment> \<open>new state\<close>
        if symbols_read_from_tapes!0 = 0 then 
        let len =(length symbols_read_from_tapes);
        directions = (two_tapes_move_right k1 k2 len)
          in
       (zip symbols_read_from_tapes  directions)
      else 
        let 
        len =(length symbols_read_from_tapes);
        directions =(two_tapes_move_left k1 k2 len)
          in
       (zip symbols_read_from_tapes  directions)
      )
)"

(*TODO *)
fun add_two_tape::"nat\<Rightarrow>nat\<Rightarrow>command"  where
"add_two_tape k1 k2=(\<lambda>l. (0,[])) "

(*TODO *)
fun sub_two_tape::"nat\<Rightarrow>nat\<Rightarrow>command"  where
"sub_two_tape k1 k2=(\<lambda>l. (0,[])) "

(*
datatype aexp =  A atomExp            |
                 Plus atomExp atomExp |
                 Sub atomExp atomExp  | 
                 Parity atomExp       |
                 RightShift atomExp
*)

fun atomExp_TM::"(vname\<Rightarrow>nat) \<Rightarrow>atomExp \<Rightarrow> nat \<Rightarrow>machine" where
"atomExp_TM idd (N a) s =(write_nat_tape a s)"|
"atomExp_TM idd (V v) s =[copy_tape (idd v) s]"


(* TODO *)

fun Aexp_TM::"(vname\<Rightarrow>nat)\<Rightarrow>aexp \<Rightarrow>machine " where
"Aexp_TM idd (A a ) = atomExp_TM idd a 1"|
"Aexp_TM idd (Plus a1 a2) = (atomExp_TM idd a1 1);;( atomExp_TM idd a2 2);;[add_two_tape 1 2]"|
"Aexp_TM idd (Sub a1 a2) = (atomExp_TM idd a1 1);; (atomExp_TM idd a2 2);;[sub_two_tape 1 2]"|
"Aexp_TM idd (Parity a) = []"|
"Aexp_TM idd (RightShift a) = []"

(*
TODO:read value from a tape
*)
fun tape_list_read::"nat \<Rightarrow>nat" where
" tape_list_read k = 0"

(*
datatype
  com = SKIP 
      | Assign vname aexp      
      | Seq    com  com         
      | If     vname com com     
      | While  vname com
*)
(* IF cond THEN M1 ELSE M2 ENDIF*)
(*(symbol list \<Rightarrow> bool)*)


(*
text \<open>
The loops are while loops consisting of a head and a body. The body is a Turing
machine that is executed in every iteration as long as the condition in the
head of the loop evaluates to true. The condition is of the same form as in
branching TMs, namely a predicate over the symbols read from the tapes.
Sometimes this is not expressive enough, and so we allow a Turing machine as
part of the loop head that is run prior to evaluating the condition. In most
cases, however, this TM is empty.
\<close>

definition turing_machine_loop :: "machine \<Rightarrow> (symbol list \<Rightarrow> bool) \<Rightarrow> machine \<Rightarrow> machine"
  ("WHILE _ ; _ DO _ DONE" 60)
where
  "WHILE M1 ; cond DO M2 DONE \<equiv>
    M1 @
    [cmd_jump cond (length M1 + 1) (length M1 + length M2 + 2)] @
    (relocate (length M1 + 1) M2) @
    [cmd_jump (\<lambda>_. True) 0 0]"
*)

(*
definition turing_machine_branch :: "(symbol list \<Rightarrow> bool) \<Rightarrow> machine \<Rightarrow> machine \<Rightarrow> machine"
  ("IF _ THEN _ ELSE _ ENDIF" 60)
where
  "IF cond THEN M1 ELSE M2 ENDIF \<equiv>
    [cmd_jump cond 1 (length M1 + 2)] @
    (relocate 1 M1) @
    [cmd_jump (\<lambda>_. True) (length M1 + length M2 + 2) 0] @
    (relocate (length M1 + 2) M2)"
*)

(* TODO: cond*)

(* ? ? ? *)

fun while_TM_aux::" com\<Rightarrow>(vname\<Rightarrow>nat) \<Rightarrow>nat \<Rightarrow> machine" where
"while_TM_aux   SKIP idd k  = []"|
"while_TM_aux  (Assign v a) idd k  = (Aexp_TM idd a);;[copy_tape 1 (idd v)] "|
"while_TM_aux  (Seq c1 c2) idd k = (while_TM_aux c1 idd k);;(while_TM_aux c2 idd k)"|
"while_TM_aux  (If v c1 c2) idd k =IF (\<lambda>x. True) THEN (while_TM_aux c1 idd k) ELSE (while_TM_aux c1 idd k) ENDIF"|
"while_TM_aux  (While  v c) idd k = (while_TM_aux  (If v c SKIP) idd k);;while_TM_aux  (While  v c) idd k"



definition while_TM ::"com \<Rightarrow>machine" where
"while_TM c =while_TM_aux c (num_variable c) (card(count_com_variable c)+3)"



theorem while_TM_is_Turing:"turing_machine 5 (card(count_com_variable c)) (while_TM c)"
  sorry

(* the first tape is not needed, so I will let it be empty for the sake of convenience*)
(*definition start_config :: "nat \<Rightarrow> symbol list \<Rightarrow> config" where
  "start_config k xs \<equiv> (0, (\<lfloor>xs\<rfloor>, 0) # replicate (k - 1) (\<lfloor>[]\<rfloor>, 0))"
*)
abbreviation cfg0 ::"com \<Rightarrow>config" where
"cfg0 c \<equiv> start_config (card(count_com_variable c)) []"


theorem while_TM_halts :
  assumes "\<exists>n. (c,(\<lambda>x. 0)) \<Rightarrow>\<^bsup> n \<^esup> t"
  shows " halts (while_TM c) (cfg0 c) "

  sorry


(* transforms_turing_machine_sequential *)
(* 
lemma transforms_turing_machine_sequential:
  assumes "transforms M1 tps1 t1 tps2" and "transforms M2 tps2 t2 tps3"
  shows "transforms (M1 ;; M2) tps1 (t1 + t2) tps3"
*)

(*
definition running_time :: "machine \<Rightarrow> config \<Rightarrow> nat" where
  "running_time M cfg \<equiv> LEAST t. fst (execute M cfg t) = length M"
*)

theorem while_TM_in_exp_time:
  assumes " (com,s) \<Rightarrow>\<^bsup> n \<^esup> t"
  
  shows "running_time "
  "running_time M cfg \<le> 3*n*n"


end