(*  Title:  Refinements/hol_to_imp_tactics_base.ML
    Author: Kevin Kappelmann
    Author: Max Lang

Basics to run IMP programs, track their states changes, and prove their
correspondence with HOL programs.
*)
signature HOL_TO_IMP_TACTICS_BASE =
sig
  include HAS_LOGGER

  type HOL_eqs_retrieval = Proof.context -> term -> thm list option
  val get_HOL_eqs : HOL_eqs_retrieval

  val seq_tac: thm -> Proof.context -> int -> tactic
  val assign_tac: thm -> Proof.context -> int -> tactic
  val call_tac: thm -> Proof.context -> thm list -> int -> tactic
  val if_tac: thm -> Proof.context -> int -> tactic
  val run_step_tac: ('a -> tactic) -> ('a -> tactic) -> ('a -> tactic) -> ('a -> tactic) -> 'a -> tactic
  val run_tac: (int -> tactic) -> int -> tactic
end

structure HOL_To_IMP_Tactics_Base : HOL_TO_IMP_TACTICS_BASE =
struct

val logger = Logger.setup_new_logger HOL_to_IMP_base_logger "HOL_To_IMP_Tactics_Base"

structure TU = Tactic_Util
structure SUT = State_Update_Tracking

(*find theorems of the form "f x = ...", given f possibly applied to some arguments*)
type HOL_eqs_retrieval = Proof.context -> term -> thm list option

(*FIXME: create a more robust filter*)
fun get_HOL_eqs ctxt t =
  let val thms = Find_Theorems.find_theorems ctxt NONE NONE true [
      (*search for the head constant*)
      (true, Find_Theorems.Pattern (head_of t)),
      (*ignore conditional rules*)
      (false, Find_Theorems.Pattern @{term "(\<Longrightarrow>)"})
    ] |> snd |> map snd
  in if null thms then NONE else SOME thms end

(* tactics for assign, seq, and if that run one step of the program, given the appropriate theorems *)

(*applies a theorem of the form: assumes "?P1 c1" and "?P2 c2" shows "?P (Seq c1 c2)" *)
fun seq_tac seq_thmI ctxt = resolve_tac ctxt [seq_thmI]

fun simp_update_tac ctxt =
  (*simplify expression*)
  TRY o safe_simp_tac ctxt
  (*substitute all (created) state retrievals*)
  THEN' TRY o SUT.subst_all_STATE_interp_retrieve_key_tac ctxt
  (*final simplification with assumptions*)
  THEN' TRY o safe_asm_simp_tac ctxt

(*applies a theorem of the following form and solves the premise:
assumes "s' = (STATE (interp_state st))(k := eval exp s)"
shows "?P (Assign k exp) (STATE (interp_state st))"*)
fun assign_tac assign_thmI ctxt =
  resolve_tac ctxt [assign_thmI]
  (*solve state update assumption*)
  THEN' SUT.STATE_interp_update_eq_STATE_interp_fun_upd (simp_update_tac ctxt) ctxt

fun call_tac call_thmI ctxt correctness =
  resolve_tac ctxt [call_thmI]
  (*solve correctness assumption*)
  THEN' resolve_tac ctxt correctness
  (*solve state update assumption*)
  THEN' SUT.STATE_interp_update_eq_STATE_interp_fun_upd (simp_update_tac ctxt) ctxt

(*
assumes "s vb = v"
and "PROP SIMPS_TO_UNIF (v \<noteq> 0) b1"
and "PROP SIMPS_TO_UNIF (\<not>b1) b2"
and "b1 \<Longrightarrow> ?P c c1 s"
and "b2 \<Longrightarrow> ?P c c2 s"
shows "?P s (If vb c1 c2)"
*)
fun if_tac if_thmI ctxt =
  let
    fun SIMP_TO_UNIF_condition_tac ctxt = Simps_To_Unif.SIMPS_TO_UNIF_refl_tac
      (TRY o safe_asm_simp_tac ctxt) ~1 ctxt
    val finish_contradictory_branch = SOLVED' (safe_asm_full_simp_tac ctxt)
  in
    resolve_tac ctxt [if_thmI]
    THEN' SUT.STATE_interp_retrieve_key_eq_tac (HOL_To_IMP_Util.refl_tac ctxt) ctxt
    THEN' SIMP_TO_UNIF_condition_tac ctxt
    THEN' SIMP_TO_UNIF_condition_tac ctxt
    (*close possibly contradictory branches*)
    THEN' TRY o (fn i => finish_contradictory_branch i ORELSE finish_contradictory_branch (i + 1))
  end

(*run one (seq assign ...), (seq call ...), or if step of a program*)
fun run_step_tac seq_tac assign_tac call_tac if_tac =
  (seq_tac THEN' (assign_tac ORELSE' call_tac))
  ORELSE' if_tac

(*usage: run_tac (run_step_tac ...)*)
val run_tac = TRY oo REPEAT_ALL_NEW

end
