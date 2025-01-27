theory FAS_Definition
  imports
    Graph_Theory.Digraph
    Graph_Theory.Arc_Walk
begin

definition feedback_arc_set :: "(('a,'b) pre_digraph * nat) set" where
  "feedback_arc_set \<equiv> {(H, k). fin_digraph H \<and> (\<exists> S.
    S \<subseteq> arcs H \<and> card S \<le> k \<and> (\<forall> p. pre_digraph.cycle H p  \<longrightarrow> (\<exists> e \<in> S. e \<in> set p)))}"

lemma feedback_arc_set_cert:
  assumes "S \<subseteq> arcs H"
  and "fin_digraph H"
  and "card S \<le> k"
  and "(\<forall> p. pre_digraph.cycle H p  \<longrightarrow> (\<exists> e \<in> S. e \<in> set p))"
  shows "(H,k) \<in> feedback_arc_set"
  using assms feedback_arc_set_def by blast

end