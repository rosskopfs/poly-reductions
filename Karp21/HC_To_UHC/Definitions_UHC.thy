section \<open>HC to UHC\<close>

theory Definitions_UHC
  imports Main Graph_Theory.Digraph Graph_Theory.Arc_Walk
    Graph_Theory.Vertex_Walk
    "../VC_To_HC/Definitions_HC"
    "Poly_Reductions_Lib.Vwalk_Cycle"
begin

subsection\<open>Preliminaries\<close>

(*pre_digraph.cycle already assumes that every node is only contained once*)
(*Case for empty c is already in cycle*)
definition
  "is_uhc (G::('a,('a \<times> 'a)) pre_digraph) (c:: 'a list)  \<equiv>
    ((vwalk_cycle G c \<and> (\<forall>x\<in> verts G. x \<in> set c)\<and> distinct (tl c))\<or> card (verts G) \<le> 1)
    \<and> set c \<subseteq> verts G"

definition
  "uhc \<equiv> {G. \<exists>c. wf_digraph G \<and> symmetric G \<and> is_uhc G c \<and>((tail G = fst \<and> head G = snd)
    \<or> arcs G = {}) \<and> finite (verts G)}"

fun to_cycle_hc where
"to_cycle_hc ((a, b)#vs) = (if b = 1 then a#(to_cycle_hc vs) else to_cycle_hc vs)" |
"to_cycle_hc [] = []"

(*last two edge sets are not part of the original proof, but are needed for case with only one node*)
(*I'm using the "\<or> arcs = {}" to easily construct a graph that is not in uhc. If arcs are empty,
head and tail are not important*)
definition "hc_to_uhc \<equiv>
  \<lambda>(G::('a, ('a \<times> 'a)) pre_digraph).
  (if wf_digraph G \<and> ((tail G = fst \<and> head G = snd) \<or> arcs G = {}) then
    (if finite (verts G) then
      (if card (verts G) > 1 then
        \<lparr>verts = {(v, (0::nat))|v. v \<in> verts G} \<union> {(v, 1)|v. v \<in> verts G} \<union> {(v, 2)|v. v \<in> verts G},
        arcs = {((v, 0), (v, 1))|v. v \<in> verts G} \<union>{((v, 1), (v, 0))|v. v \<in> verts G}\<union>
          {((v, 1), (v, 2))|v. v \<in> verts G}\<union>{((v, 2), (v, 1))|v. v \<in> verts G}\<union>
          {((v, 2), (u, 0))|v u e. e \<in> arcs G \<and> v = tail G e \<and> u = head G e \<and> u \<noteq> v}\<union>
          {((u, 0), (v, 2))|v u e. e \<in> arcs G \<and> v = tail G e \<and> u = head G e \<and> u \<noteq> v},
        tail = fst, head = snd\<rparr>
        else \<lparr>verts = {}, arcs = {}, tail = fst, head = snd\<rparr>)
    else \<lparr>verts = {(v, 0)|v. v \<in> verts G}, arcs = {}, tail = fst, head = snd\<rparr>)
  else (let x = (SOME x. x \<in> arcs G)
    in \<lparr>verts = {}, arcs = {((head G x, 0), (head G x, 1))}, tail = fst, head = snd\<rparr>))"

lemma verts_empt_arcs_not_not_wf_digraph:
  assumes "verts G = {}" "arcs G \<noteq> {}"
  shows "\<not> wf_digraph G"
  using assms wf_digraph_def by fast

lemma else_not_in_uhc_1:
  assumes "G' = (let x = (SOME x. x \<in> arcs G)
    in \<lparr>verts = {}, arcs = {((head G x, 0), (head G x, 1))}, tail = fst, head = snd\<rparr>)"
      "\<not> wf_digraph G"
    shows "G' \<notin> uhc"
  using assms unfolding wf_digraph_def uhc_def by(auto simp add: Let_def)

lemma else_not_in_uhc_2:
  assumes "G' = (let x = (SOME x. x \<in> arcs G)
    in \<lparr>verts = {}, arcs = {((head G x, 0), (head G x, 1))}, tail = fst, head = snd\<rparr>)"
      "\<not>((tail G = fst \<and> head G = snd) \<or> arcs G = {})"
  shows "G' \<notin> uhc"
  using assms unfolding uhc_def wf_digraph_def by (auto simp add: Let_def)

lemma else_not_in_uhc_3:
  assumes "G' = \<lparr>verts = {(v, 0)|v. v \<in> verts G}, arcs = {}, tail = fst, head = snd\<rparr>"
      "\<not> finite (verts G)"
    shows "G' \<notin> uhc"
proof -
  have "verts G' = (verts G) \<times> {0}"
    using assms
    by auto
  then have "\<not> finite (verts G')"
    using assms finite_cartesian_productD1
    by fastforce
  then show ?thesis
    using uhc_def
    by blast
qed

lemma else_not_in_uhc:
  assumes "G' = (let x = (SOME x. x \<in> arcs G)
    in \<lparr>verts = {}, arcs = {((head G x, 0), (head G x, 1))}, tail = fst, head = snd\<rparr>)"
      "\<not>(wf_digraph G \<and> ((tail G = fst \<and> head G = snd) \<or> arcs G = {}))"
    shows "G' \<notin> uhc"
  using else_not_in_uhc_1 else_not_in_uhc_2 assms by blast

lemma G_leq_1_vertex_in_uhc:
  assumes "G \<in> hc" "\<not>card (verts G) >1"
  shows "hc_to_uhc G \<in> uhc"
  using assms
  unfolding hc_def hc_to_uhc_def uhc_def wf_digraph_def is_uhc_def
    symmetric_def arcs_ends_def sym_def
  by auto

end
