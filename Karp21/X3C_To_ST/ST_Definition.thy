theory ST_Definition
  imports Tree_Enumeration.Tree_Graph 
begin

(* Definition of the Steiner Tree problem *)

type_synonym 'a steiner_tree_tuple = "('a set \<times> 'a edge set \<times> ('a edge \<Rightarrow> nat) \<times> 'a set \<times> nat)" 
definition steiner_tree :: "'a steiner_tree_tuple set" where
  "steiner_tree \<equiv> 
    { (V, E, w, R, k). fin_ulgraph V E \<and> R \<subseteq> V \<and>
      (\<exists> Tv Te. tree Tv Te  \<and> subgraph Tv Te V E \<and> R \<subseteq> Tv \<and> (\<Sum>e \<in> Te. w e) \<le> k) }"


lemma steiner_tree_cert:
  assumes "tree Tv Te"
          "fin_ulgraph V E"
          "R \<subseteq> V"
          "subgraph Tv Te V E"
          "R \<subseteq> Tv"
          "(\<Sum>e \<in> Te. w e) \<le> k"
  shows "(V, E, w, R, k) \<in> steiner_tree"
  using assms steiner_tree_def by fastforce

end 
