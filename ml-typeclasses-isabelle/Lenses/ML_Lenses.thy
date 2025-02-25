\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory ML_Lenses
  imports
    ML_ICategories
begin

ML_file\<open>lens.ML\<close>

(*standard function space lense*)
ML\<open>structure SLens =
  Lens(structure L = Lens_Base(Arrow_Apply(SArrow_Apply)); structure A = Arrow(SArrow_Apply))\<close>

end