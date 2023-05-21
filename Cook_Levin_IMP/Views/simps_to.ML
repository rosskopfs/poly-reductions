(*  Title: simps_to.ML
    Author: Kevin Kappelmann

Set up and solve SIMPS_TO goals.
*)
signature SIMPS_TO =
sig

  val dest_SIMPS_TO : term -> (term * term)
  val dest_SIMPS_TO_prop : term -> (term * term)

  val mk_SIMPS_TO_cprop : cterm -> cterm -> cterm
  val mk_SIMPS_TO_var_cprop : Proof.context -> cterm -> cterm

  val finish_SIMPS_TO_tac : int -> tactic
  val SIMPS_TO_tac : (int -> tactic) -> int -> tactic

  val SIMPS_TO_thmsq : (int -> tactic) -> Proof.context -> cterm -> thm Seq.seq
  val SIMPS_TO_thm_resultsq : (int -> tactic) -> Proof.context -> cterm ->
    (thm * cterm) Seq.seq

end

structure Simps_To : SIMPS_TO =
struct

structure Util = View_Util

val dest_SIMPS_TO = \<^Const_fn>\<open>SIMPS_TO _ for lhs rhs => \<open>(lhs, rhs)\<close>\<close>
val dest_SIMPS_TO_prop = dest_SIMPS_TO o HOLogic.dest_Trueprop

fun mk_SIMPS_TO_cprop clhs crhs = \<^instantiate>\<open>'a = \<open>Thm.ctyp_of_cterm clhs\<close> and clhs and crhs
  in cprop\<open>SIMPS_TO clhs crhs\<close> for clhs :: 'a\<close>

fun mk_SIMPS_TO_var_cprop ctxt ct =
  Var (("x", Thm.maxidx_of_cterm ct + 1), Thm.typ_of_cterm ct)
  |> Thm.cterm_of ctxt
  |> mk_SIMPS_TO_cprop ct

val finish_SIMPS_TO_tac = resolve0_tac @{thms SIMPS_TOI}
fun SIMPS_TO_tac tac = tac THEN' finish_SIMPS_TO_tac

fun SIMPS_TO_thmsq tac = Util.HEADGOAL (Util.apply_tac (SIMPS_TO_tac tac)) oo mk_SIMPS_TO_var_cprop

val SIMPS_TO_thm_resultsq =
  Seq.map (fn thm => (thm, Thm.cconcl_of thm |> Util.cdest_Trueprop |> Thm.dest_arg))
  ooo SIMPS_TO_thmsq


end