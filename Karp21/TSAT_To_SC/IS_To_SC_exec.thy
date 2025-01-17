section \<open>\<open>Independent Set\<close> To \<open>Set Cover\<close> on lists\<close>

theory IS_To_SC_exec
  imports IS_To_SC VC_SC_Definition_exec Poly_Reductions_Lib.Tr_Fun_Defs
begin

subsection \<open>Independent Set to Vertex Cover\<close>

definition
  "is_vc_exec ≡ \<lambda>(E, k). if k > length (remdups (concat E)) then (E, k) else (E, length (remdups (concat E)) - k)"


subsubsection ‹‹is_vc_exec› is related to ‹is_vc››

lemma is_vc_exec_rel[transfer_rule]:
  "(IS_List_rel ===> VC_List_rel) is_vc is_vc_exec"
  unfolding is_vc_def is_vc_exec_def IS_List_rel_iff by transfer_prover

theorem is_reduction_is_vc_exec: "is_reduction is_vc_exec independent_set_exec vertex_cover_exec"
  unfolding independent_set_exec_def vertex_cover_exec_def
  by (rule transfer_is_reduction[OF is_reduction_is_vc[unfolded independent_set_unfold_pred vertex_cover_unfold_pred]])
    (fact independent_set_pred_exec_rel vertex_cover_pred_exec_rel is_vc_exec_rel transl_IS_list_set_rel)+


subsubsection ‹Tail recursive definition of ‹is_vc_exec››

definition
  "is_vc_exec_tr ≡ \<lambda>(E, k). if k > length_tr (remdups_tr (concat_tr E)) then (E, k) else (E, length_tr (remdups_tr (concat_tr E)) - k)"

lemma is_vc_exec_tr_eq: "is_vc_exec_tr = is_vc_exec"
  unfolding is_vc_exec_def is_vc_exec_tr_def tr_simps by (rule refl)



subsection \<open>Vertex Cover to Set Cover\<close>

definition
  "vc_sc' \<equiv> \<lambda>(E, k).
    if ugraph E \<and> k \<le> card (\<Union> E) then (
      (λV. let
        p1 = (λe. (e, V)) ` E;
        p2 = Set.filter (λ(e, v). v ∈ e) p1;
        p3 = (λ(e, v). e) ` p2
      in p3) ` (⋃ E),
      k)
    else ({{undefined}}, 0)"

lemma vc_sc'_eq: "vc_sc = vc_sc'"
proof -
  have "{e. e ∈ E ∧ v ∈ e} = (λ(e, v). e) ` (Set.filter (λ(e, v). v ∈ e) ((λe. (e, v)) ` E))"
    for E::"'a set set" and v by force
  then have "{{e. e \<in> E \<and> v \<in> e} | v. v \<in> \<Union>E} =
      (λv. (\<lambda>(e, v). e) ` (Set.filter (λ(e, v). v ∈ e) ((λe. (e, v)) ` E))) ` (⋃ E)"
    for E::"'a set set" by auto
  then show ?thesis
    unfolding vc_sc_def vc_sc'_def by presburger
qed

definition
  "vc_sc_exec \<equiv> \<lambda>(E, k).
    if ugraph_exec E \<and> k \<le> length (remdups (concat E)) then (
      map (λV. let
        p1 = map (λe. (e, V)) E;
        p2 = filter (λ(e, v). ListMem v e) p1;
        p3 = map (λ(e, v). e) p2
      in p3) (concat E),
      k)
    else ([[undefined]], 0)"


subsubsection ‹‹vc_sc_exec› is related to ‹vc_sc››

lemma member_ListMem_rel[transfer_rule]: "((=) ===> Set_List_rel_eq ===> (=)) (∈) ListMem"
  by (fastforce simp: ListMem_iff)

lemma image_map_rel[transfer_rule]: "((r ===> s) ===> Set_List_rel r ===> Set_List_rel s) image map"
  by (fastforce simp: rel_set_def dest: rel_funD)

lemma filter_rel[transfer_rule]: "((r ===> (=)) ===> Set_List_rel r ===> Set_List_rel r) Set.filter filter"
  by (fastforce simp: rel_set_def dest: rel_funD)

(* TODO: get rid of undefined in vc_sc (non-exec version)*)
lemma undefined_set_list_rel[transfer_rule]: "Set_List_rel_eq undefined undefined"
  sorry

lemma vc_sc_exec_rel[transfer_rule]:
  "(VC_List_rel ===> SC_List_rel) vc_sc vc_sc_exec"
  unfolding vc_sc'_eq vc_sc'_def vc_sc_exec_def VC_List_rel_iff SC_List_rel_iff Let_def
  by transfer_prover

theorem is_reduction_vc_sc_exec: "is_reduction vc_sc_exec vertex_cover_exec set_cover_exec"
  unfolding vertex_cover_exec_def set_cover_exec_def
  by (rule transfer_is_reduction[OF is_reduction_vc_sc[unfolded vertex_cover_unfold_pred set_cover_unfold_pred]])
    (fact vertex_cover_pred_exec_rel set_cover_pred_exec_rel vc_sc_exec_rel transl_VC_list_set_rel)+


subsubsection ‹Tail recursive definition of ‹vc_sc_exec››

definition
  "ugraph_exec_tr \<equiv> list_all_tr (\<lambda>xs. length_tr (remdups_tr xs) = 2)"

lemma ugraph_exec_tr_eq: "ugraph_exec_tr = ugraph_exec"
  unfolding ugraph_exec_tr_def ugraph_exec_def tr_simps by (rule refl)

definition
  "vc_sc_exec_tr \<equiv> \<lambda>(E, k).
    if ugraph_exec_tr E \<and> k \<le> length_tr (remdups_tr (concat_tr E)) then (
      map_tr (λV. let
        p1 = map_tr (λe. (e, V)) E;
        p2 = filter_tr (λ(e, v). ListMem_tr v e) p1;
        p3 = map_tr (λ(e, v). e) p2
      in p3) (concat_tr E),
      k)
    else ([[undefined]], 0)"

lemma vc_sc_exec_tr_eq: "vc_sc_exec_tr = vc_sc_exec"
  unfolding vc_sc_exec_def vc_sc_exec_tr_def ugraph_exec_tr_eq tr_simps by (rule refl)

end
