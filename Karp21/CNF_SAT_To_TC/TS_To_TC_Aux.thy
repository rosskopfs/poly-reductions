theory TS_To_TC_Aux
  imports Main "../TSAT_To_SC/TSAT_To_SC"
begin


subsection \<open>Order over Litarals of a CNF clause\<close>

fun extract_value :: "'a lit \<Rightarrow> 'a" where
  "extract_value (Pos a) = a"
| "extract_value (Neg a) = a"

fun is_Pos :: "'a lit \<Rightarrow> bool" where
  "is_Pos (Pos _) = True"
| "is_Pos _ = False"

instantiation lit :: (linorder) linorder
begin

definition less_eq_lit where [simp]: "x \<le> y \<equiv>
  extract_value x < extract_value y \<or> (extract_value x = extract_value
y \<and> is_Pos x \<le> is_Pos y)"

definition less_lit where [simp]: "(x:: 'a lit) < y \<equiv> (x\<le>y \<and> x\<noteq>y)"

instance
  by standard (fastforce elim!: is_Pos.elims(3) extract_value.elims)+

end

(* Ordered by Pos/Neg then by order over a' type *)
datatype 'a lit' = Pos' 'a | Neg' 'a

instantiation lit' :: (linorder) linorder
begin

fun less_eq_lit' :: "'a lit' \<Rightarrow> 'a lit' \<Rightarrow> bool" where
  "less_eq_lit' (Neg' x) (Neg' y) = (x \<le> y)"
| "less_eq_lit' (Neg' _) (Pos' _) = True"
| "less_eq_lit' (Pos' _) (Neg' _) = False"
| "less_eq_lit' (Pos' x) (Pos' y) = (x \<le> y)"

definition less_lit' where [simp]: "(x:: 'a lit') < y \<longleftrightarrow> (x\<le>y \<and> x\<noteq>y)"

instance
  apply standard
  apply (auto elim!: less_eq_lit'.elims)
  using less_eq_lit'.elims(3) by fastforce
end

subsection \<open>CNF Aux for TS_To_TC\<close>


lemma cnf_remove_clause: "F \<in> three_cnf_sat \<Longrightarrow> F = F' @ [a] \<Longrightarrow> F' \<in> three_cnf_sat"
proof -
  assume asm1: "F\<in> three_cnf_sat" 
  assume asm2: "F = F' @ [a]"
  from asm1 obtain \<sigma> where obt1:"\<sigma> \<Turnstile> F " unfolding three_cnf_sat_def sat_def by auto
  from asm2 have "(set F') \<subseteq> (set F)" by auto
  from this obt1 have "\<sigma> \<Turnstile> F'" unfolding models_def
    by blast
  from asm1 asm2 this show ?thesis 
  unfolding three_cnf_sat_def sat_def 
  by auto
qed


lemma cnf_clause: "F \<in> three_cnf_sat \<Longrightarrow> F = F' @ [a] \<Longrightarrow> [a] \<in> three_cnf_sat"
proof -
  assume asm1: "F\<in> three_cnf_sat" 
  assume asm2: "F = F' @ [a]"
  from asm1 obtain \<sigma> where obt1:"\<sigma> \<Turnstile> F " unfolding three_cnf_sat_def sat_def by auto
  from asm2 have "(set [a]) \<subseteq> (set F)" by auto
  from this obt1 have "\<sigma> \<Turnstile> [a]" unfolding models_def
    by blast
  from asm1 asm2 this show ?thesis 
  unfolding three_cnf_sat_def sat_def 
  by auto
qed




subsection \<open>Graph Aux for TS_To_TC\<close>


fun var :: "'a lit \<Rightarrow> 'a "  where
   "var (Pos v) = v"
 | "var (Neg v) = v"

fun tolit :: "'a lit \<Rightarrow> 'a \<Rightarrow> 'a lit "  where
   "tolit (Pos v) = Pos"
 | "tolit (Neg v) = Neg"

fun isPos :: "'a lit \<Rightarrow> bool " where
   "isPos (Pos v) = True"
 | "isPos (Neg v) = False"

lemma i_split:"i< length (F@[c]) \<longleftrightarrow> (i < length F) \<or> (i = length F)" 
  by auto

lemma and_distrLit2:"
  \<And>l1 l2 l3 i . ((
  (i < length (F)  \<and> {l1,l2,l3} = (F@[c]) ! i ) \<or> 
  (i = length F  \<and> {l1,l2,l3} = (F@[c]) ! i )) \<and> 
  sorted_list_of_set ((F@[c])  !i) = [l1,l2,l3]) 
  \<longleftrightarrow>
  (i < length (F)  \<and> {l1,l2,l3} = (F@[c]) ! i \<and> (sorted_list_of_set ((F@[c])  !i) = [l1,l2,l3]) ) \<or> 
  ((i = length F  \<and> {l1,l2,l3} = (F@[c]) ! i ) \<and> (sorted_list_of_set ((F@[c])  !i) = [l1,l2,l3]))" 
  by auto


lemma i_less_lengthF:
      "(i < length (F)  \<and> {l1,l2,l3} = (F@[c]) ! i \<and> (sorted_list_of_set ((F@[c])  !i) = [l1,l2,l3]) ) =
       (i < length (F)  \<and> {l1,l2,l3} = (F) ! i \<and> (sorted_list_of_set ((F)  !i) = [l1,l2,l3]) )"
  by (simp add: nth_append)

lemma i_eq_lengthF:
      "(i = length (F)  \<and> {l1,l2,l3} = (F@[c]) ! i \<and> (sorted_list_of_set ((F@[c])  !i) = [l1,l2,l3]) ) =
       (i = length (F)  \<and> {l1,l2,l3} = c \<and> (sorted_list_of_set (c) = [l1,l2,l3]) )"
  by fastforce


lemma orToUnion:" 
  \<Union>{{{(1::nat,tolit l1 = Pos,var l1,0::nat),(2,False,i,0)}, 
      {(1,tolit l2 = Pos,var l2,0),(2,False,i,1)}, 
      {(1,tolit l3 = Pos,var l3,0),(2,False,i,2)}} |l1 l2 l3 i. 
                    (i < length F  \<and> {l1,l2,l3} = F ! i \<and> sorted_list_of_set (F!i) = [l1,l2,l3]) \<or> 
                    (i = length F  \<and> {l1,l2,l3} = c  \<and> sorted_list_of_set (c) = [l1,l2,l3])} =  
  \<Union>{{{(1,tolit l1 = Pos,var l1,0),(2,False,i,0)}, 
      {(1,tolit l2 = Pos,var l2,0),(2,False,i,1)}, 
      {(1,tolit l3 = Pos,var l3,0),(2,False,i,2)}} |l1 l2 l3 i. 
      (i < length F  \<and> {l1,l2,l3} = F ! i \<and> sorted_list_of_set (F!i) = [l1,l2,l3])} \<union>   
  \<Union>{{{(1,tolit l1 = Pos,var l1,0),(2,False,i,0)}, 
      {(1,tolit l2 = Pos,var l2,0),(2,False,i,1)}, 
      {(1,tolit l3 = Pos,var l3,0),(2,False,i,2)}} |l1 l2 l3 i. 
      (i = length F  \<and> {l1,l2,l3} = c  \<and> sorted_list_of_set (c) = [l1,l2,l3])}"
  by auto blast +


(* To run in Isabelle2022: restore old syntax *)
abbreviation "strict_sorted \<equiv> sorted_wrt (<)"

lemma sorted_to_strict_sorted:"card c = 3 \<Longrightarrow> c= {l1,l2,l3} \<Longrightarrow> sorted [l1,l2,l3] \<Longrightarrow> 
                              strict_sorted [l1,l2,l3]"
proof -
  assume asms: "card c = 3" "c= {l1,l2,l3}" "sorted [l1,l2,l3]"
  from this have "card {l1,l2,l3} = 3"
    by simp
  from this have "l1 \<noteq> l2 \<and> l2 \<noteq> l3 \<and> l1 \<noteq> l3" 
    by (metis card_2_iff doubleton_eq_iff insert_absorb2 is_singletonI is_singleton_altdef
 not_numeral_less_one numeral_eq_iff numeral_less_iff semiring_norm(77) semiring_norm(89))
  from this asms show ?thesis
    by auto
qed


lemma sorted_strictsorted_lits2_2 :"c = {la,lb,lc} \<Longrightarrow> (la::nat lit) < lb \<Longrightarrow> lb < lc  \<Longrightarrow>  
      sorted_list_of_set c = [la,lb,lc]"
proof -
  assume asms:"c = {la,lb,lc}" "(la::nat lit) < lb" "lb < lc"
  from this have "la < lc" 
    using less_trans by blast
  from this asms have " strict_sorted [la,lb,lc]"
    by simp 
  from this asms(1) show "sorted_list_of_set c = [la,lb,lc]"
    by simp
qed



lemma sorted_strictsorted_lits4:"c = {l1,l2,l3} \<Longrightarrow> card c = 3 \<Longrightarrow> 
        sorted [(l1::nat lit),l2,l3] \<Longrightarrow> 
        sorted_list_of_set c = [l1,l2,l3]"  
proof -
  assume asms:  "c = {l1,l2,l3}" "card c = 3" "sorted [(l1::nat lit),l2,l3]"
  from this have strict:"strict_sorted [l1, l2, l3]" using sorted_to_strict_sorted
    by blast
  from this have l1l2less:"l1< l2"
    by simp
  from strict have l2l3less:"l2 < l3"
    by simp
  from this asms(1) l1l2less show "sorted_list_of_set c = [l1,l2,l3]" 
    using sorted_strictsorted_lits2_2[where c = c and la = l1 and lb = l2 and lc = l3]
    by blast
qed


lemma union_split:"\<Union>{{{(1::nat,tolit l1 = Pos,var l1,0::nat),(2,False,i,0)}, 
      {(1,tolit l2 = Pos,var l2,0),(2,False,i,1)}, 
      {(1,tolit l3 = Pos,var l3,0),(2,False,i,2)}}| 
      l1 l2 l3 i . i < length (F@[c]) \<and> {l1,l2,l3} = (F@[c]) ! i \<and> sorted_list_of_set ((F@[c])  !i) = [l1,l2,l3]} 
      = 
      \<Union>{{{(1,tolit l1 = Pos,var l1,0),(2,False,i,0)}, 
      {(1,tolit l2 = Pos,var l2,0),(2,False,i,1)}, 
      {(1,tolit l3 = Pos,var l3,0),(2,False,i,2)}}| 
      l1 l2 l3 i . i < length (F) \<and> {l1,l2,l3} = (F) ! i \<and> sorted_list_of_set ((F)  !i) = [l1,l2,l3]} \<union>
      \<Union>{{{(1,tolit l1 = Pos,var l1,0),(2,False,i,0)}, 
      {(1,tolit l2 = Pos,var l2,0),(2,False,i,1)}, 
      {(1,tolit l3 = Pos,var l3,0),(2,False,i,2)}}| 
      l1 l2 l3 i . i = length F \<and> {l1,l2,l3} = c \<and> sorted_list_of_set c = [l1,l2,l3]}"
proof -
  define A where A_def:"A=
    \<Union>{{{(1::nat,tolit l1 = Pos,var l1,0::nat),(2,False,i,0)}, 
      {(1,tolit l2 = Pos,var l2,0),(2,False,i,1)}, 
      {(1,tolit l3 = Pos,var l3,0),(2,False,i,2)}}| 
      l1 l2 l3 i . i < length (F@[c]) \<and> {l1,l2,l3} = (F@[c]) ! i \<and> 
      sorted_list_of_set ((F@[c])  !i) = [l1,l2,l3]}" 


  define B where B_def:"B=
    \<Union>{{{(1::nat,tolit l1 = Pos,var l1,0::nat),(2,False,i,0)}, 
      {(1,tolit l2 = Pos,var l2,0),(2,False,i,1)}, 
      {(1,tolit l3 = Pos,var l3,0),(2,False,i,2)}}| 
      l1 l2 l3 i . (i < length (F) \<or> i = length F) \<and> {l1,l2,l3} = (F@[c]) ! i \<and> 
      sorted_list_of_set ((F@[c])  !i) = [l1,l2,l3]}"


  define C where C_def:"C=
    \<Union>{{{(1::nat,tolit l1 = Pos,var l1,0::nat),(2,False,i,0)}, 
      {(1,tolit l2 = Pos,var l2,0),(2,False,i,1)}, 
      {(1,tolit l3 = Pos,var l3,0),(2,False,i,2)}}| 
      l1 l2 l3 i . 
      ((i < length (F)  \<and> {l1,l2,l3} = (F@[c]) ! i ) \<or> 
      (i = length F  \<and> {l1,l2,l3} = (F@[c]) ! i )) \<and> 
      sorted_list_of_set ((F@[c])  !i) = [l1,l2,l3]}"


  define D where D_def:"D=
    \<Union>{{{(1::nat,tolit l1 = Pos,var l1,0::nat),(2,False,i,0)}, 
      {(1,tolit l2 = Pos,var l2,0),(2,False,i,1)}, 
      {(1,tolit l3 = Pos,var l3,0),(2,False,i,2)}}| 
      l1 l2 l3 i . (
      (i < length F  \<and> {l1,l2,l3} = F ! i \<and> sorted_list_of_set (F!i) = [l1,l2,l3]) \<or> 
      (i = length F  \<and> {l1,l2,l3} = c  \<and> sorted_list_of_set (c) = [l1,l2,l3]) )}"


  define E where E_def:"E=
      \<Union>{{{(1::nat,tolit l1 = Pos,var l1,0::nat),(2,False,i,0)}, 
      {(1,tolit l2 = Pos,var l2,0),(2,False,i,1)}, 
      {(1,tolit l3 = Pos,var l3,0),(2,False,i,2)}}| 
      l1 l2 l3 i .
      (i < length F  \<and> {l1,l2,l3} = F ! i \<and> sorted_list_of_set (F!i) = [l1,l2,l3])} \<union>
      \<Union>{{{(1,tolit l1 = Pos,var l1,0),(2,False,i,0)}, 
      {(1,tolit l2 = Pos,var l2,0),(2,False,i,1)}, 
      {(1,tolit l3 = Pos,var l3,0),(2,False,i,2)}}| 
      l1 l2 l3 i .  
      (i = length F  \<and> {l1,l2,l3} = c  \<and> sorted_list_of_set (c) = [l1,l2,l3])}"

  have step1:"A = B" 
    using i_split[where F = F and c = c]
    unfolding A_def B_def
    by simp
  have step2:"B = C" 
    unfolding B_def C_def
    by meson
  have step3: "C = D" 
    unfolding C_def D_def
    using and_distrLit2[where F= F and c= c] 
          i_less_lengthF[where F= F and c = c] 
          i_eq_lengthF[where F= F and c = c]
    by presburger
  have "D = E" 
    unfolding D_def E_def
    using orToUnion[where F=F and c= c]
    by fast
  from this step1 step2 step3 have "A=E"
    by simp
  from this A_def E_def show ?thesis
    by simp
qed

lemma clauseToEdges:"card c = 3 \<Longrightarrow> c = {lita,litb,litc} \<Longrightarrow> sorted [lita,litb,litc] \<Longrightarrow> 
      \<Union>{{{(1,tolit l1 = Pos,var l1,0),(2,False,i,0)}, 
      {(1,tolit l2 = Pos,var l2,0),(2,False,i,1)}, 
      {(1,tolit l3 = Pos,var l3,0),(2,False,i,2)}}| 
      l1 l2 l3 i . i = length F \<and> {l1,l2,l3} = c \<and> sorted_list_of_set c = [l1,l2,l3]} 
      = 
      {{(1::nat,tolit lita = Pos,var lita,0::nat),(2,False,length F,0)},
      {(1::nat,tolit litb = Pos,var litb,0::nat),(2,False,length F,1)},
      {(1::nat,tolit litc = Pos,var litc,0::nat),(2,False,length F,2)}}"
proof -
  assume asms:"card c = 3" "c = {lita,litb,litc}" "sorted [lita,litb,litc]" 
  from asms have lit_sorted:"sorted_list_of_set {lita,litb,litc} = [lita,litb,litc]"
    using sorted_strictsorted_lits4
    by blast
  from this asms(2) show ?thesis
    by simp
qed




lemma clause_split_union:"c = {lita, litb, litc} \<Longrightarrow> sorted [lita, litb, litc] \<Longrightarrow>  card c = 3  \<Longrightarrow>
      \<Union>{{{(1::nat,tolit l1 = Pos,var l1,0::nat),(2,False,i,0)}, 
      {(1,tolit l2 = Pos,var l2,0),(2,False,i,1)}, 
      {(1,tolit l3 = Pos,var l3,0),(2,False,i,2)}}| 
      l1 l2 l3 i . i < length (F@[c]) \<and> {l1,l2,l3} = (F@[c]) ! i \<and> sorted_list_of_set ((F@[c])  !i) = [l1,l2,l3]} 
      = 
      \<Union>{{{(1,tolit l1 = Pos,var l1,0),(2,False,i,0)}, 
      {(1,tolit l2 = Pos,var l2,0),(2,False,i,1)}, 
      {(1,tolit l3 = Pos,var l3,0),(2,False,i,2)}}| 
      l1 l2 l3 i . i < length (F) \<and> {l1,l2,l3} = (F) ! i \<and> sorted_list_of_set ((F)  !i) = [l1,l2,l3]} \<union> 
      {{(1,tolit lita = Pos,var lita,0),(2,False,length F,0)}, 
      {(1,tolit litb = Pos,var litb,0),(2,False,length F,1)}, 
      {(1,tolit litc = Pos,var litc,0),(2,False,length F,2)}}"
proof -
  assume asms: "c = {lita, litb, litc}" "sorted [lita, litb, litc]" "card c = 3"
  define A where A_def:"A =
    \<Union>{{{(1::nat,tolit l1 = Pos,var l1,0::nat),(2,False,i,0)}, 
      {(1,tolit l2 = Pos,var l2,0),(2,False,i,1)}, 
      {(1,tolit l3 = Pos,var l3,0),(2,False,i,2)}}| 
      l1 l2 l3 i . i < length (F@[c]) \<and> {l1,l2,l3} = (F@[c]) ! i \<and> sorted_list_of_set ((F@[c])  !i) = [l1,l2,l3]}"
  define B where B_def:"B =
    \<Union>{{{(1::nat,tolit l1 = Pos,var l1,0::nat),(2,False,i,0)}, 
      {(1,tolit l2 = Pos,var l2,0),(2,False,i,1)}, 
      {(1,tolit l3 = Pos,var l3,0),(2,False,i,2)}}| 
      l1 l2 l3 i . i < length (F) \<and> {l1,l2,l3} = (F) ! i \<and> sorted_list_of_set ((F)  !i) = [l1,l2,l3]} \<union>
      \<Union>{{{(1,tolit l1 = Pos,var l1,0),(2,False,i,0)}, 
      {(1,tolit l2 = Pos,var l2,0),(2,False,i,1)}, 
      {(1,tolit l3 = Pos,var l3,0),(2,False,i,2)}}| 
      l1 l2 l3 i . i = length F \<and> {l1,l2,l3} = c \<and> sorted_list_of_set c = [l1,l2,l3]}"    
  define C where C_def: "C =  
      \<Union> {{{(1::nat, tolit l1 = Pos, var l1, 0::nat), (2, False, i, 0)}, 
          {(1, tolit l2 = Pos, var l2, 0), (2, False, i, 1)},
          {(1, tolit l3 = Pos, var l3, 0), (2, False, i, 2)}} |
          l1 l2 l3 i. i < length F \<and> {l1, l2, l3} = F ! i \<and> 
          sorted_list_of_set (F ! i) = [l1, l2, l3]} \<union>
      {{(1,tolit lita = Pos,var lita,0),(2,False,length F,0)}, 
      {(1,tolit litb = Pos,var litb,0),(2,False,length F,1)}, 
      {(1,tolit litc = Pos,var litc,0),(2,False,length F,2)}}"
  have step1:"A = B" 
    unfolding A_def B_def
    using union_split
    by presburger
  from asms have "B= C"
    unfolding B_def C_def
    using clauseToEdges[where c = c and F = F and lita = lita and litb = litb and litc = litc]
    by presburger
  from this step1 have "A = C"
    by simp
  from this show ?thesis
    unfolding A_def C_def
    by fast
qed


subsection "finite Aux"

lemma finite1:
"F\<in> three_cnf_sat \<Longrightarrow> 
finite {{(0, False, 0, 2), (Suc 0, True, var l, 0)} |j l. l \<in>  \<Union> (set F)} " 
proof -
  assume "F\<in> three_cnf_sat" 
  from this have "finite (\<Union> (set F))" unfolding three_cnf_sat_def sat_def models_def
    using finite_Union by fastforce
  from this have fin1:"finite (var`(\<Union> (set F)))" by auto
  let ?S = "({0}\<times>{True,False} \<times> (var`(\<Union> (set F)))\<times> {2})\<times>({1}\<times>{True,False} \<times> (var`(\<Union> (set F)))\<times> {0})"
  from fin1 show ?thesis by (fastforce intro: finite_surj[where A = "?S"]) 
qed

lemma finite2:
"F\<in> three_cnf_sat \<Longrightarrow> 
finite {{(0, False, 0, 2), (Suc 0, False, var l, 0)} |j l. l \<in>  \<Union> (set F)} " 
proof -
  assume "F\<in> three_cnf_sat" 
  from this have "finite (\<Union> (set F))" unfolding three_cnf_sat_def sat_def models_def
    using finite_Union by fastforce
  from this have fin1:"finite (var`(\<Union> (set F)))" by auto
  let ?S = "({1}\<times>{True,False} \<times> {0}\<times> {0})\<times>({1}\<times>{True,False} \<times> (var`(\<Union> (set F)))\<times> {0})"
  from fin1 show ?thesis by (fastforce intro: finite_surj[where A = "?S"]) 
qed


lemma finite3:
"F\<in> three_cnf_sat \<Longrightarrow> 
finite {{(Suc 0, False, var l, 0), (Suc 0, True, var l, 0)} |l. \<exists>x\<in>set F. l \<in> x}" 
proof -
  assume "F\<in> three_cnf_sat" 
  from this have "finite (\<Union> (set F))" unfolding three_cnf_sat_def sat_def models_def
    using finite_Union by fastforce
  from this have fin1:"finite (var`(\<Union> (set F)))" by auto
  let ?S = "({1}\<times>{True,False} \<times> (var`(\<Union> (set F)))\<times> {0})\<times>({1}\<times>{True,False} \<times> (var`(\<Union> (set F)))\<times> {0})"
  from fin1 show ?thesis by (fastforce intro: finite_surj[where A = "?S"]) 
qed



lemma finite4:
"F\<in> three_cnf_sat \<Longrightarrow> 
finite
     (\<Union> {{{(Suc 0, tolit l1 = Pos, var l1, 0), (2, False, i, 0)},
           {(Suc 0, tolit l2 = Pos, var l2, 0), (2, False, i, Suc 0)},
           {(Suc 0, tolit l3 = Pos, var l3, 0), (2, False, i, 2)}} |
          l1 l2 l3 i. i < length F \<and> {l1, l2, l3} = F ! i \<and> sorted_list_of_set ((F)  !i) = [l1,l2,l3]})" 
proof -
  assume "F\<in> three_cnf_sat" 
  from this have "finite (\<Union> (set F))" unfolding three_cnf_sat_def sat_def models_def
    using finite_Union by fastforce
  from this have fin1:"finite (var`(\<Union> (set F)))" by auto
  let ?S = "({1}\<times>{True,False} \<times> (var`(\<Union> (set F)))\<times> {0})\<times>({2}\<times>{True,False} \<times> {0..<length F}\<times> {0,1,2})"
  from fin1 show ?thesis by (fastforce intro: finite_surj[where A = "?S"]) 
qed



end
