theory IMP_Minus_To_IMP_Minus_Minus_State_Translations_nat
  imports IMP_Minus_To_IMP_Minus_Minus_State_Translations Primitives Binary_Arithmetic_Nat
begin

fun dropWhile_char:: "nat \<Rightarrow> nat" where
  "dropWhile_char n =
    (if n = 0
     then 0
     else if hd_nat n = encode_char (CHR ''#'')
          then dropWhile_char (tl_nat n)
          else n
    )"

lemma subdropWhile_char: "dropWhile_char v = dropWhile_nat (\<lambda>i. i = encode_char (CHR ''#'')) v"
  by (induct v rule: dropWhile_char.induct) simp

fun takeWhile_char:: "nat \<Rightarrow> nat" where
  "takeWhile_char n =
    (if n = 0
     then 0
     else if hd_nat n = encode_char (CHR ''#'')
          then (hd_nat n) ## takeWhile_char (tl_nat n)
          else 0
    )"

lemma subtakeWhile_char: "takeWhile_char v =  takeWhile_nat (\<lambda>i. i = encode_char (CHR ''#'')) v"
  by ((induct v rule: takeWhile_char.induct), simp, metis)

fun takeWhile_char_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "takeWhile_char_acc acc n =
    (if n = 0
     then acc
     else if hd_nat n = encode_char (CHR ''#'')
          then takeWhile_char_acc ((hd_nat n) ## acc) (tl_nat n)
          else acc
    )"

lemma takeWhile_char_append:
  "takeWhile_char xs = xs \<Longrightarrow> takeWhile_char (append_nat xs ys) = append_nat xs (takeWhile_char ys)"
proof -
  assume "takeWhile_char xs = xs"
  moreover obtain xs' ys' where "xs = list_encode xs'"  "ys = list_encode ys'"
    by (metis list_decode_inverse)
  ultimately show ?thesis
    by (simp del: takeWhile_char.simps takeWhile_nat.simps add: subtakeWhile_char sub_takeWhile
        sub_append list_encode_eq)
qed

lemma append_nat_cons: "append_nat xs (a ## ys) = append_nat (append_nat xs (a ## 0)) ys"
proof -
  obtain xs' ys' where "xs = list_encode xs'"  "ys = list_encode ys'"
    by (metis list_decode_inverse)
  thus ?thesis by(simp del: list_encode.simps add: cons0 sub_cons sub_append)
qed

lemma takeWhile_char_extend:
  "takeWhile_char xs = xs \<Longrightarrow>
    takeWhile_char (append_nat xs ((encode_char CHR ''#'') ## 0))
      = append_nat xs ((encode_char CHR ''#'') ## 0)"
proof -
  assume "takeWhile_char xs = xs"
  moreover obtain xs' where "xs = list_encode xs'"
    by (metis list_decode_inverse)
  ultimately show ?thesis
    by(simp del: takeWhile_char.simps takeWhile_nat.simps list_encode.simps add: cons0
        subtakeWhile_char sub_takeWhile list_encode_eq sub_append)
qed

lemma takeWhile_char_induct:
  "takeWhile_char xs = xs \<Longrightarrow>
    takeWhile_char (append_nat xs ys)
      = reverse_nat (takeWhile_char_acc (reverse_nat (takeWhile_char xs)) ys)"
  apply (induct ys arbitrary:xs rule:length_nat.induct)
   apply (simp del: takeWhile_char_acc.simps takeWhile_char.simps add: append_nat_0)
   apply (simp add: rev_rev_nat)
  apply (simp only: takeWhile_char_append)
  apply (subst takeWhile_char.simps)
  apply (auto simp del: takeWhile_char_acc.simps takeWhile_char.simps)
  subgoal for v xs
    apply (subst append_nat_cons[of xs])
    apply (simp add: takeWhile_char_extend del: takeWhile_char_acc.simps
        takeWhile_char.simps)
    apply (subst (2) takeWhile_char_acc.simps)
    apply (simp add: reverse_append_nat reverse_singleton_nat append_singleton_nat
        del: takeWhile_char_acc.simps takeWhile_char.simps)
    done
  apply (subst takeWhile_char_acc.simps)
  apply (auto simp add:append_nat_0  rev_rev_nat simp del: takeWhile_char_acc.simps
      takeWhile_char.simps)
  done

definition takeWhile_char_tail:: "nat \<Rightarrow> nat" where
  "takeWhile_char_tail ys = reverse_nat (takeWhile_char_acc 0 ys)"

lemma subtail_takeWhile_char:
  "takeWhile_char_tail ys = takeWhile_char ys"
  using takeWhile_char_induct[of 0]
  by (simp add: reverse_nat_0 takeWhile_char_tail_def)

definition var_to_var_bit_nat:: "nat \<Rightarrow> nat" where
  "var_to_var_bit_nat v =
    (if length_nat v > 0
     then (if hd_nat v = encode_char (CHR ''#'')
           then (let t = dropWhile_char v;
                     l = length_nat (takeWhile_char v) - 1
                 in (if length_nat t > 0 \<and> hd_nat t = encode_char (CHR ''$'')
                     then some_nat (prod_encode(tl_nat t, l))
                     else 0))
           else 0)
     else 0
    )"

definition var_to_var_bit_tail:: "nat \<Rightarrow> nat" where
  "var_to_var_bit_tail v =
    (if length_nat v > 0
     then (if hd_nat v = encode_char (CHR ''#'')
           then (let t = dropWhile_char v;
                     l = length_nat (takeWhile_char_tail v) - 1
                 in (if length_nat t > 0 \<and> hd_nat t = encode_char (CHR ''$'')
                     then some_nat (prod_encode(tl_nat t, l))
                     else 0))
           else 0)
     else 0
    )"

lemma subtail_var_to_var_bit: "var_to_var_bit_tail v = var_to_var_bit_nat v"
  by (simp only: var_to_var_bit_tail_def var_to_var_bit_nat_def subtail_takeWhile_char)

fun vname_nat_encode:: "vname * nat \<Rightarrow> nat" where
  "vname_nat_encode (v, n) = prod_encode (vname_encode v, n)"

fun vname_nat_decode:: "nat \<Rightarrow> vname * nat" where
  "vname_nat_decode n = (let (v, x) = prod_decode n in (vname_decode v, x))"

lemma vne[simp]: "vname_nat_decode (vname_nat_encode x) = x"
  by (metis old.prod.case prod_encode_inverse vname_id vname_nat_decode.simps
      vname_nat_encode.elims)

fun vname_nat_option_encode:: "(vname * nat) option \<Rightarrow> nat" where
  "vname_nat_option_encode None = 0" |
  "vname_nat_option_encode (Some x) = some_nat (vname_nat_encode x)"

fun vname_nat_option_decode:: "nat \<Rightarrow> (vname * nat) option" where
  "vname_nat_option_decode 0 = None" |
  "vname_nat_option_decode (Suc n) = Some (vname_nat_decode n)"

lemma vname_nat_option_id[simp]: "vname_nat_option_decode (vname_nat_option_encode x) = x"
  by (metis option.exhaust vne some_nat_def vname_nat_option_decode.simps
      vname_nat_option_encode.simps)

lemma lambda_encode_char: "(\<lambda>i. i = encode_char x) \<circ> encode_char = (\<lambda>i. i = x)"
  by (auto simp add: idchar)

lemma sub_var_to_var_bit:
  "var_to_var_bit_nat (vname_encode v) = vname_nat_option_encode (var_to_var_bit v)"
  by (auto simp only: subtakeWhile_char subdropWhile_char var_to_var_bit_nat_def vname_encode_def
      sub_length sub_hd sub_dropWhile sub_takeWhile Let_def sub_tl var_to_var_bit_def
      sub_head_map sub_tail_map List.dropWhile_map List.takeWhile_map length_map idchar
      lambda_encode_char vname_nat_option_encode.simps vname_nat_encode.simps split:if_splits)

fun n_hashes_nat :: "nat \<Rightarrow> nat" where
  "n_hashes_nat 0 = 0" |
  "n_hashes_nat (Suc n) = cons (encode_char (CHR ''#'')) (n_hashes_nat n)"

lemma sub_n_hashes: "n_hashes_nat n = vname_encode (n_hashes n)"
  by (induct n) (auto simp :vname_encode_def sub_cons)

fun n_hashes_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "n_hashes_acc acc 0  = acc" |
  "n_hashes_acc acc (Suc n) = n_hashes_acc ((encode_char (CHR ''#'')) ## acc) n"

lemma n_hashes_dashes:
  "reverse_nat (n_hashes_nat (Suc m)) = (encode_char CHR ''#'') ## reverse_nat (n_hashes_nat m)"
  by (induction m)
    (simp add: sub_cons sub_reverse sub_n_hashes vname_encode_def list_encode_eq
      del: list_encode.simps)+

lemma n_hashes_induct:
  "n_hashes_nat (m + n) = reverse_nat (n_hashes_acc (reverse_nat (n_hashes_nat m)) n)"
proof(induct n arbitrary: m)
  case 0
  then show ?case by (simp add: rev_rev_nat)
next
  case (Suc n)
  then show ?case
    by (metis add_Suc_shift n_hashes_acc.simps(2) n_hashes_dashes)
qed

definition n_hashes_tail::"nat \<Rightarrow> nat" where
  "n_hashes_tail n = reverse_nat (n_hashes_acc 0 n)"

lemma subtail_n_hashes: "n_hashes_tail n = n_hashes_nat n"
  using n_hashes_induct[of 0 n]
  by (auto simp del: n_hashes_acc.simps simp add:reverse_nat_0 n_hashes_tail_def)

definition var_bit_to_var_nat:: "nat \<Rightarrow> nat" where
  "var_bit_to_var_nat vk =
  append_nat (append_nat (n_hashes_nat (snd_nat vk + 1)) (vname_encode ''$'')) (fst_nat vk)"

definition var_bit_to_var_tail:: "nat \<Rightarrow> nat" where
  "var_bit_to_var_tail vk =
  append_tail (append_tail (n_hashes_tail (snd_nat vk + 1)) (vname_encode ''$'')) (fst_nat vk)"

lemma subtail_var_bit_to_var:
  "var_bit_to_var_tail vk = var_bit_to_var_nat vk"
  by (simp only:subtail_append var_bit_to_var_nat_def var_bit_to_var_tail_def subtail_n_hashes)

lemma sub_var_bit_to_var:
  "var_bit_to_var_nat (vname_nat_encode vk) = vname_encode (var_bit_to_var vk)"
  by (cases vk) (auto simp only: var_bit_to_var_nat_def sub_snd vname_nat_encode.simps sub_n_hashes
      vname_encode_def sub_append sub_fst fst_def var_bit_to_var_def, simp)

lemma prod_encode_bounded[simp]:" 0 < snd_nat p \<Longrightarrow> prod_encode (fst_nat p, snd_nat p - Suc 0) < p"
proof -
  assume a:"0 < snd_nat p"
  obtain x y where  "prod_decode p = (x,y)"
    by fastforce
  hence xy_def: "p = prod_encode (x,y)"
    by (metis prod_decode_inverse)
  thus ?thesis
    using a
    by (simp add: sub_fst sub_snd xy_def)
      (smt Suc_pred a add.commute add.right_neutral add_Suc add_le_cancel_left
        cancel_comm_monoid_add_class.diff_cancel lessI less_eq_nat.simps(1) less_le_trans not_le
        prod_decode_aux.simps prod_encode_def prod_encode_prod_decode_aux split_conv)
qed

fun operand_bit_to_var_nat:: "nat \<Rightarrow> nat" where
  "operand_bit_to_var_nat p  =
    (if snd_nat p = 0
     then cons (fst_nat p) 0
     else cons (fst_nat p) (operand_bit_to_var_nat (prod_encode (fst_nat p, snd_nat p - 1)))
    )"

fun operand_bit_to_var_acc:: " nat \<Rightarrow> nat \<Rightarrow> nat" where
  "operand_bit_to_var_acc acc p  =
  (if snd_nat p = 0
   then acc
   else (operand_bit_to_var_acc ((fst_nat p) ## acc) (prod_encode (fst_nat p, snd_nat p - 1)))
  )"

lemma operand_bit_to_var_induct:
  "operand_bit_to_var_nat (prod_encode (c, n + m)) =
    operand_bit_to_var_acc (operand_bit_to_var_nat (prod_encode (c, n))) (prod_encode (c, m))"
proof(induct m arbitrary: n)
  case 0
  then show ?case
    by (simp add: sub_snd)
next
  case (Suc m)
  then show ?case
    by ((simp add: sub_fst sub_snd del: operand_bit_to_var_nat.simps operand_bit_to_var_acc.simps),
        (simp only: Suc_plus), (simp add: sub_fst sub_snd))
qed

definition operand_bit_to_var_tail:: "nat \<Rightarrow> nat" where
  "operand_bit_to_var_tail p = operand_bit_to_var_acc (cons (fst_nat p) 0) p"

lemma subtail_operand_bit_to_var:
  "operand_bit_to_var_tail p = operand_bit_to_var_nat p"
proof -
  obtain c m where "p = prod_encode (c,m)"
    by (metis operand_bit_to_var_acc.cases prod_decode_inverse)
  thus ?thesis using operand_bit_to_var_induct[of c 0 m]
    by(simp add: operand_bit_to_var_tail_def sub_fst sub_snd)
qed

fun char_nat_encode ::"char * nat \<Rightarrow> nat " where
  "char_nat_encode (x, n) = prod_encode (encode_char x, n)"

fun char_nat_decode ::" nat \<Rightarrow> (char * nat) " where
  "char_nat_decode p = (let (x, n) = prod_decode p in (decode_char x, n))"

lemma char_nat_decode_inverse[simp]: "char_nat_decode (char_nat_encode x) = x"
  by (simp add: idcharorg)
    (metis case_prod_beta char_nat_encode.simps comp_apply id_apply idcharorg prod.exhaust_sel
      prod.sel(1) prod_encode_inverse snd_conv)

lemma sub_operand_bit_to_var:
  "operand_bit_to_var_nat (char_nat_encode p) = vname_encode (operand_bit_to_var p)"
proof(cases p)
  case (Pair a b) thus ?thesis
    by (induct b arbitrary: p) (simp add: cons_def sub_fst sub_snd vname_encode_def)+
qed

definition var_to_operand_bit_nat:: "nat \<Rightarrow> nat" where
  "var_to_operand_bit_nat v =
  (if v \<noteq> 0 \<and> v = (operand_bit_to_var_nat (prod_encode (hd_nat v, length_nat v - 1)))
   then some_nat (prod_encode (hd_nat v, length_nat v - 1))
   else 0
  )"

definition var_to_operand_bit_tail:: "nat \<Rightarrow> nat" where
  "var_to_operand_bit_tail v =
  (if v \<noteq> 0 \<and> v = (operand_bit_to_var_tail (prod_encode (hd_nat v, length_nat v - 1)))
   then some_nat (prod_encode (hd_nat v, length_nat v - 1))
   else 0
  )"

lemma subtail_var_to_operand_bit: "var_to_operand_bit_tail v = var_to_operand_bit_nat v"
  by (simp only: var_to_operand_bit_tail_def var_to_operand_bit_nat_def subtail_operand_bit_to_var)

fun char_nat_option_encode:: "(char * nat) option \<Rightarrow> nat" where
  "char_nat_option_encode None = 0" |
  "char_nat_option_encode (Some x) = Suc (char_nat_encode x)"

fun char_nat_option_decode :: "nat \<Rightarrow> (char*nat) option" where
  "char_nat_option_decode 0 = None" |
  "char_nat_option_decode (Suc n) = Some (char_nat_decode n)"

lemma char_nat_option_id[simp]: "char_nat_option_decode (char_nat_option_encode x) = x"
  by (cases x) (auto simp add: decode_char_def encode_char_def)

lemma sub_head_enc_map: "vname_encode v \<noteq> 0 \<Longrightarrow> head (map encode_char v) = encode_char (hd v)"
  by (simp add: vname_encode_def list_encode_eq sub_head_map flip: list_encode.simps)

lemma list_encode_non_empty: "(list_encode xs = 0) = (xs = [])"
  using list_encode_eq by fastforce

lemma sub_var_to_operand_bit:
  "var_to_operand_bit_nat (vname_encode v) = char_nat_option_encode (var_to_operand_bit v)"
  by (simp only: var_to_operand_bit_nat_def vname_encode_def sub_hd sub_length length_map
      var_to_operand_bit_def sub_some) (smt char_nat_encode.simps char_nat_option_encode.simps
      option_encode.simps(2) vname_encode_def vname_id sub_operand_bit_to_var sub_head_enc_map
      list_encode_non_empty map_is_Nil_conv)

definition IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_list::
  "(vname,val) assignment list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> vname \<Rightarrow> bit option" where
  "IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_list s n a b v =
  (case var_to_var_bit v of
    Some (v', k) \<Rightarrow> if k < n then Some (nth_bit (fun_list_find s v') k) else None |
    None \<Rightarrow> (case var_to_operand_bit v of
              Some (CHR ''a'', k) \<Rightarrow> if k < n then Some (nth_bit a k) else None |
              Some (CHR ''b'', k) \<Rightarrow> if k < n then Some (nth_bit b k) else None |
    _ \<Rightarrow> (if v = ''carry'' then Some Zero else None))
  )"

lemma sublist_IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b:
  "IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_list s n a b v
    = IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b (fun_of s) n a b v"
  by (simp only: IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_list_def
      sub_fun_list_find IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_def)

definition IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_nat::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_nat s n a b v =
    (if var_to_var_bit_nat v \<noteq> 0
     then (let v' = fst_nat (var_to_var_bit_nat v - 1);
                k = snd_nat (var_to_var_bit_nat v - 1)
           in if k < n
              then some_nat (nth_bit_nat (fun_list_find_nat  s v') k)
              else 0)
     else (let v' = fst_nat (var_to_operand_bit_nat v - 1);
                k = snd_nat (var_to_operand_bit_nat v - 1)
             in if var_to_operand_bit_nat v \<noteq> 0 \<and> v' = encode_char (CHR ''a'')
                then if k < n
                     then Suc (nth_bit_nat a k)
                     else 0
                else if var_to_operand_bit_nat v \<noteq> 0 \<and> v' = encode_char (CHR ''b'')
                     then if k < n
                          then Suc (nth_bit_nat b k)
                          else 0
                     else if v = vname_encode (''carry'')
                           then Suc 0
                           else 0)
    )"

definition IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_tail::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_tail s n a b v =
    (if var_to_var_bit_tail v \<noteq> 0
     then (let v' = fst_nat (var_to_var_bit_tail v - 1);
                k = snd_nat (var_to_var_bit_tail v - 1)
           in if k < n
              then some_nat (nth_bit_tail (fun_list_find_tail s v') k)
              else 0)
     else (let v' = fst_nat (var_to_operand_bit_tail v - 1);
                k = snd_nat (var_to_operand_bit_tail v - 1)
           in if var_to_operand_bit_tail v \<noteq> 0 \<and> v' = encode_char (CHR ''a'')
              then if k < n
                   then Suc (nth_bit_tail a k)
                   else 0
              else if var_to_operand_bit_tail v \<noteq> 0 \<and> v' = encode_char (CHR ''b'')
                   then if k < n
                        then Suc (nth_bit_tail b k)
                        else 0
                   else (if v = vname_encode (''carry'') then Suc 0 else 0))
    )"

lemma subtail_IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b:
  "IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_tail s n a b v
    = IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_nat s n a b v"
  by (simp only: IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_tail_def
      IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_nat_def subtail_var_to_operand_bit
      subtail_nth_bit subtail_var_to_var_bit subtail_fun_list_find)

lemma impm_assignment_simp: "impm_assignment_encode = prod_encode o (\<lambda>(x, y). (vname_encode x, y))"
  by fastforce

lemma vname_inj_simp: "(vname_encode x = vname_encode y) = (x = y)"
  using vname_inj by (auto simp add: inj_def)

lemma char_inj_simp: "(encode_char x = encode_char y) = (x=y)"
  using idchar by (auto simp add: inj_def)

lemma vname_nat_option_encode_0: "(vname_nat_option_encode x = 0) = (x = None)"
  by (cases x) auto

lemma bit_option_encode_0: "(bit_option_encode x = 0) = (x = None)"
  by (cases x) auto

lemma char_nat_option_encode_0: "(char_nat_option_encode x = 0) = (x = None)"
  by (cases x) auto

lemma subnat_IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b:
  "IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_nat
    (impm_assignment_list_encode s) n a b (vname_encode v)
      = bit_option_encode (IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_list s n a b v)"
  apply (cases "var_to_var_bit v")
   apply (cases "var_to_operand_bit v")
    apply (simp add: IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_list_def
      IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_nat_def sub_var_to_operand_bit
      sub_var_to_var_bit vname_inj_simp)
   apply (simp add: IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_nat_def )
   apply (auto simp only: vname_inj Let_def sub_nth_bit vname_nat_option_encode.simps
      vname_inj_simp sub_var_to_var_bit)[1]
    apply simp
   apply (simp add:sub_snd sub_fst bit_option_encode_0 char_inj_simp sub_var_to_operand_bit
      IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_list_def)
   apply (smt char.case char.exhaust)
  apply (simp add: IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_nat_def sub_var_to_var_bit)
  apply (auto simp only: vname_inj sub_snd  sub_fst fst_def sub_nth_bit vname_nat_encode.simps
      IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_list_def impm_assignment_list_encode_def
      impm_assignment_simp sub_fun_list_find_nat inj_fun_list_find simp flip: One_nat_def map_map,
      simp)[1]
  done

definition IMP_Minus_State_To_IMP_Minus_Minus_partial_list::
  "(vname, nat) assignment list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> vname \<Rightarrow> bit option" where
  "IMP_Minus_State_To_IMP_Minus_Minus_partial_list s n r v =
    (case var_to_var_bit v of
      Some (v', k) \<Rightarrow>
        if k \<ge> n
        then None
        else if k < r
              then map_list_find (map (\<lambda>(x, y). (x, nth_bit y k)) s) v'
              else Some Zero |
      None \<Rightarrow>
        (case var_to_operand_bit v of
          Some (CHR ''a'', k) \<Rightarrow>
            if k < n
            then Some Zero
            else None |
          Some (CHR ''b'', k) \<Rightarrow>
            if k < n
            then Some Zero
            else None |
          _ \<Rightarrow>
            if v = ''carry''
            then Some Zero
            else None
        )
    )"

lemma sub_lambda_partial:
  "((\<lambda>x. Some (nth_bit x k)) \<circ>\<^sub>m map_of s) v' = map_list_find (map (\<lambda>(x, y). (x, nth_bit y k)) s) v'"
  by (induct s) (auto simp add: map_comp_def)

lemma sublist_IMP_Minus_State_To_IMP_Minus_Minus_partial:
  "IMP_Minus_State_To_IMP_Minus_Minus_partial_list s n r v
    = IMP_Minus_State_To_IMP_Minus_Minus_partial (map_of s) n r v"
  by (simp only:IMP_Minus_State_To_IMP_Minus_Minus_partial_list_def sub_lambda_partial
      IMP_Minus_State_To_IMP_Minus_Minus_partial_def)

fun map_IMP_Minus_State_To_IMP_Minus_Minus_partial:: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "map_IMP_Minus_State_To_IMP_Minus_Minus_partial k n =
    (if n = 0
     then 0
     else (prod_encode (fst_nat (hd_nat n), nth_bit_nat (snd_nat (hd_nat n)) k)) ##
           map_IMP_Minus_State_To_IMP_Minus_Minus_partial k (tl_nat n)
    )"

fun map_IMP_Minus_State_To_IMP_Minus_Minus_partial_acc:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "map_IMP_Minus_State_To_IMP_Minus_Minus_partial_acc acc k n =
    (if n = 0
     then acc
     else
      map_IMP_Minus_State_To_IMP_Minus_Minus_partial_acc
        ((prod_encode (fst_nat (hd_nat n), nth_bit_nat (snd_nat (hd_nat n)) k)) ## acc) k (tl_nat n)
    )"

lemma submap_IMP_Minus_State_To_IMP_Minus_Minus_partial:
  "map_IMP_Minus_State_To_IMP_Minus_Minus_partial k s
     = map_nat (\<lambda>n. prod_encode(fst_nat n, nth_bit_nat (snd_nat n) k)) s"
  by (induct k s rule: map_IMP_Minus_State_To_IMP_Minus_Minus_partial.induct) simp

lemma map_IMP_Minus_state_append:
  "map_IMP_Minus_State_To_IMP_Minus_Minus_partial k (append_nat xs ys)
    = append_nat (map_IMP_Minus_State_To_IMP_Minus_Minus_partial k xs)
                 (map_IMP_Minus_State_To_IMP_Minus_Minus_partial k ys)"
proof -
  obtain xs' ys' where  "xs = list_encode xs'" "ys = list_encode ys'"
    by (metis list_decode_inverse)
  thus ?thesis
    by (simp del:map_IMP_Minus_State_To_IMP_Minus_Minus_partial.simps map_nat.simps add: sub_map
        submap_IMP_Minus_State_To_IMP_Minus_Minus_partial sub_append)
qed

lemma map_IMP_Minus_State_To_IMP_Minus_Minus_partial_induct:
  "map_IMP_Minus_State_To_IMP_Minus_Minus_partial k (append_nat xs ys)
    = reverse_nat
        (map_IMP_Minus_State_To_IMP_Minus_Minus_partial_acc
          (reverse_nat (map_IMP_Minus_State_To_IMP_Minus_Minus_partial k xs)) k ys)"
  apply(induct ys arbitrary: xs rule: length_nat.induct)
   apply(simp add: append_nat_0  del: map_IMP_Minus_State_To_IMP_Minus_Minus_partial.simps
      map_IMP_Minus_State_To_IMP_Minus_Minus_partial_acc.simps)
   apply(subst map_IMP_Minus_State_To_IMP_Minus_Minus_partial_acc.simps)
   apply(simp add: rev_rev_nat append_nat_Suc
      del: map_IMP_Minus_State_To_IMP_Minus_Minus_partial.simps
      map_IMP_Minus_State_To_IMP_Minus_Minus_partial_acc.simps)+
  apply(subst (2) map_IMP_Minus_State_To_IMP_Minus_Minus_partial_acc.simps)
  apply(simp add:  map_IMP_Minus_state_append reverse_append_nat
      del: map_IMP_Minus_State_To_IMP_Minus_Minus_partial.simps
      map_IMP_Minus_State_To_IMP_Minus_Minus_partial_acc.simps)
  apply(subst map_IMP_Minus_State_To_IMP_Minus_Minus_partial.simps)
  apply(simp add: sub_hd cons0 sub_tl del: list_encode.simps
      map_IMP_Minus_State_To_IMP_Minus_Minus_partial.simps
      map_IMP_Minus_State_To_IMP_Minus_Minus_partial_acc.simps)
  apply(simp only: list_encode.simps)
  apply(simp add: reverse_singleton_nat append_singleton_nat)
  done

definition map_IMP_Minus_State_To_IMP_Minus_Minus_partial_tail:: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "map_IMP_Minus_State_To_IMP_Minus_Minus_partial_tail k ys =
    reverse_nat (map_IMP_Minus_State_To_IMP_Minus_Minus_partial_acc 0 k ys)"

lemma subtail_map_IMP_Minus_State_To_IMP_Minus_Minus_partial:
  "map_IMP_Minus_State_To_IMP_Minus_Minus_partial_tail k ys
    = map_IMP_Minus_State_To_IMP_Minus_Minus_partial k ys"
  using map_IMP_Minus_State_To_IMP_Minus_Minus_partial_induct[of k 0 ys]
  by (simp add: reverse_nat_0 map_IMP_Minus_State_To_IMP_Minus_Minus_partial_tail_def)

definition IMP_Minus_State_To_IMP_Minus_Minus_partial_nat:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "IMP_Minus_State_To_IMP_Minus_Minus_partial_nat s n r v =
    (let p = var_to_var_bit_nat v;
        v' = fst_nat (p - 1);
         k = snd_nat (p - 1)
     in if p \<noteq> 0
        then if k \<ge> n
             then 0
             else if k < r
                  then map_list_find_nat (map_IMP_Minus_State_To_IMP_Minus_Minus_partial k s) v'
                  else Suc 0
        else (let po = var_to_operand_bit_nat v;
                  vo = fst_nat (po-1);
                  ko = snd_nat (po-1)
              in if po \<noteq> 0 \<and> vo = encode_char CHR ''a''
                 then if ko < n
                      then Suc 0
                      else 0
                 else if po \<noteq> 0 \<and> vo = encode_char CHR ''b''
                      then if ko < n
                           then Suc 0
                           else 0
                      else if v = vname_encode ''carry''
                           then Suc 0
                           else 0)
    )"

definition IMP_Minus_State_To_IMP_Minus_Minus_partial_tail::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "IMP_Minus_State_To_IMP_Minus_Minus_partial_tail s n r v =
    (let p = var_to_var_bit_tail v;
        v' = fst_nat (p - 1);
         k = snd_nat (p - 1)
     in if p \<noteq> 0
        then if k \<ge> n
             then 0
             else if k < r
                  then map_list_find_nat (map_IMP_Minus_State_To_IMP_Minus_Minus_partial_tail k s) v'
                  else Suc 0
        else (let po = var_to_operand_bit_tail v;
                  vo = fst_nat (po-1);
                  ko = snd_nat (po-1)
              in if po \<noteq> 0 \<and> vo = encode_char CHR ''a''
                 then if ko < n
                      then Suc 0
                      else 0
                 else if po \<noteq> 0 \<and> vo = encode_char CHR ''b''
                      then if ko < n
                           then Suc 0
                           else 0
                      else if v = vname_encode ''carry''
                           then Suc 0
                           else 0)
    )"

lemma subtail_IMP_Minus_State_To_IMP_Minus_Minus_partial:
  "IMP_Minus_State_To_IMP_Minus_Minus_partial_tail s n r v
    = IMP_Minus_State_To_IMP_Minus_Minus_partial_nat s n r v"
  by (simp only: IMP_Minus_State_To_IMP_Minus_Minus_partial_tail_def
      IMP_Minus_State_To_IMP_Minus_Minus_partial_nat_def
      subtail_map_list_find subtail_var_to_operand_bit subtail_var_to_var_bit
      subtail_map_IMP_Minus_State_To_IMP_Minus_Minus_partial)

lemma snd_nat_0: "snd_nat 0 = 0"
  by (simp add: snd_nat_def prod_decode_def prod_decode_aux.simps)

lemma fst_nat_0: "fst_nat 0 = 0"
  by (simp add: fst_nat_def prod_decode_def prod_decode_aux.simps)

lemma fst_impm: "fst_nat (impm_assignment_encode x) = vname_encode (fst x)"
  by (cases x) (simp add: sub_fst)

lemma snd_impm: "snd_nat (impm_assignment_encode x) = snd x"
  by (cases x) (simp add:sub_snd)

lemma subnat_IMP_Minus_State_To_IMP_Minus_Minus_partial:
  "IMP_Minus_State_To_IMP_Minus_Minus_partial_nat
    (impm_assignment_list_encode s) n r (vname_encode v)
      = bit_option_encode (IMP_Minus_State_To_IMP_Minus_Minus_partial_list s n r v)"
  apply (cases "var_to_var_bit v")
   apply (cases "var_to_operand_bit v")
    apply (auto simp add:IMP_Minus_State_To_IMP_Minus_Minus_partial_nat_def
      impm_assignment_list_encode_def vname_nat_option_encode_0)
       apply (auto simp only: submap_IMP_Minus_State_To_IMP_Minus_Minus_partial)
       apply (auto simp only: Let_def sub_map sub_var_to_var_bit sub_snd sub_fst vname_inj_simp
      vname_nat_option_encode.simps zero_diff)
       apply (auto simp only: snd_nat_0 fst_nat_0 sub_map_list_find_nat
      simp flip: comp_def [of prod_encode "\<lambda>n.(fst_nat n,nth_bit_nat (snd_nat n) _ )"] map_map)
       apply (auto simp only: map_map comp_def fst_impm snd_impm sub_nth_bit)
       apply (auto simp add: IMP_Minus_State_To_IMP_Minus_Minus_partial_list_def sub_fst fst_nat_0
      sub_var_to_operand_bit bit_option_encode_0 char_inj_simp sub_snd)
    apply (smt char.case char.exhaust)
   apply (smt char.case char.exhaust)
  apply (induct s)
   apply (auto simp add:vname_inj_simp)
  done

definition IMP_Minus_State_To_IMP_Minus_Minus_list::
  "(vname,nat) assignment list \<Rightarrow> nat \<Rightarrow> vname \<Rightarrow> bit option" where
  "IMP_Minus_State_To_IMP_Minus_Minus_list s n v =
    IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_list s n 0 0 v"

lemma sublist_IMP_Minus_State_To_IMP_Minus_Minus:
  "IMP_Minus_State_To_IMP_Minus_Minus_list s n v
    = IMP_Minus_State_To_IMP_Minus_Minus (fun_of s) n v"
  by (simp add: IMP_Minus_State_To_IMP_Minus_Minus_list_def IMP_Minus_State_To_IMP_Minus_Minus_def
      sublist_IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b)

definition IMP_Minus_State_To_IMP_Minus_Minus_nat:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "IMP_Minus_State_To_IMP_Minus_Minus_nat s n v
    = IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_nat s n 0 0 v"

definition IMP_Minus_State_To_IMP_Minus_Minus_tail:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "IMP_Minus_State_To_IMP_Minus_Minus_tail s n v
   = IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b_tail s n 0 0 v"

lemma subtail_IMP_Minus_State_To_IMP_Minus_Minus:
  "IMP_Minus_State_To_IMP_Minus_Minus_tail s n v
    = IMP_Minus_State_To_IMP_Minus_Minus_nat s n v"
  by (simp only: IMP_Minus_State_To_IMP_Minus_Minus_tail_def
      IMP_Minus_State_To_IMP_Minus_Minus_nat_def
      subtail_IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b)

lemma subnat_IMP_Minus_State_To_IMP_Minus_Minus:
  "IMP_Minus_State_To_IMP_Minus_Minus_nat (impm_assignment_list_encode s) n (vname_encode v)
    = bit_option_encode (IMP_Minus_State_To_IMP_Minus_Minus_list s n v)"
  by (simp add: IMP_Minus_State_To_IMP_Minus_Minus_nat_def
      IMP_Minus_State_To_IMP_Minus_Minus_list_def
      subnat_IMP_Minus_State_To_IMP_Minus_Minus_with_operands_a_b)

end