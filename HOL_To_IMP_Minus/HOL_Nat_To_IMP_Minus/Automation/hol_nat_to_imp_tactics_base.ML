(*  Title:  Automation/hol_nat_to_imp_tactics_base.ML
    Author: Kevin Kappelmann
    Author: Max Lang

Basics to run IMP programs, track their states changes, and prove their
correspondence with HOL programs.
*)
signature HOL_NAT_TO_IMP_TACTICS_BASE =
sig
  include HAS_LOGGER

  type HOL_eqs_retrieval = Proof.context -> term -> thm list option
  val get_HOL_eqs : HOL_eqs_retrieval

  val get_HOL_To_IMP_finish_simps : Proof.context -> thm list

  val simp_state_update_val_tac : Proof.context -> int -> tactic

  (* Rel_nat side condition tactics *)
  val Rel_nat_step_tac : Proof.context -> int -> tactic
  val solve_Rel_nat_tac : Proof.context -> int -> tactic
  val simp_lhs_solve_Rel_nat_tac : Proof.context -> int -> tactic

  val rewrite_ne_zero_if_Rel_nat_tac : Proof.context -> int -> tactic

  val seq_tac : thm -> Proof.context -> int -> tactic
  val assign_tac : thm -> Proof.context -> int -> tactic
  val call_tac : thm -> (int -> tactic) -> Proof.context -> thm list -> int -> tactic
  val if_tac : thm -> (int -> tactic) -> Proof.context -> int -> tactic
  val run_step_tac : ('a -> tactic) -> ('a -> tactic) -> ('a -> tactic) -> ('a -> tactic) -> 'a ->
    tactic
  val run_tac : (int -> tactic) -> int -> tactic
end

structure HOL_Nat_To_IMP_Tactics_Base : HOL_NAT_TO_IMP_TACTICS_BASE =
struct

val logger = Logger.setup_new_logger HOL_Nat_To_IMP_Minus_base_logger
  "HOL_Nat_To_IMP_Tactics_Base"

structure SUT = State_Update_Tracking
structure HTIU = HOL_Nat_To_IMP_Util
structure HTHNU = HOL_To_HOL_Nat_Util

(*find theorems of the form "f x = ...", given f possibly applied to some arguments*)
type HOL_eqs_retrieval = Proof.context -> term -> thm list option

fun gen_find_unconditional_eqs eq ctxt t =
  Find_Theorems.find_theorems ctxt NONE NONE true [
    (*search for the HOL constant*)
    (true, Find_Theorems.Pattern t),
    (*search for an equality*)
    (true, Find_Theorems.Pattern eq),
    (*ignore conditional rules*)
    (false, Find_Theorems.Pattern @{term "(\<Longrightarrow>)"})
  ] |> snd

fun find_unconditional_eqs ctxt t =
  gen_find_unconditional_eqs (@{term "(=)"} |> Logic.varify_global) ctxt t
  @ gen_find_unconditional_eqs (@{term "(\<equiv>)"} |> Logic.varify_global) ctxt t

fun get_HOL_eqs ctxt t = case HOL_Fun_To_HOL_Nat_Fun.get_compiled_eq_unfolded ctxt t of
    SOME thm => SOME [thm]
  | NONE => find_unconditional_eqs ctxt (t |> head_of |> Logic.varify_global) |> map snd
      |> (fn [] => NONE | xs => SOME xs)

fun get_HOL_To_IMP_finish_simps ctxt =
  Named_Theorems.get ctxt @{named_theorems HOL_To_IMP_finish_simps}

fun simp_state_update_val_tac ctxt =
  (*simplify expression*)
  TRY o safe_simp_tac ctxt
  (*substitute all (created) state retrievals*)
  THEN' TRY o SUT.subst_all_STATE_interp_retrieve_key_tac ctxt
  (*final simplification with assumptions*)
  THEN' TRY o safe_asm_simp_tac ctxt

fun Rel_nat_step_tac ctxt =
  assume_tac ctxt
  ORELSE' Unify_Resolve_Base.unify_resolve_any_tac
    HOL_To_IMP_Unification.norms_first_higherp_decomp_comb_higher_unify
    HOL_To_IMP_Unification.first_higherp_decomp_comb_higher_unify
    (HOL_To_HOL_Nat_Util.get_Rel_nat_thms ctxt @ [@{thm refl}, @{thm rel_fun_appI}])
    ctxt

fun solve_Rel_nat_tac ctxt =
  SOLVED' (Rel_nat_step_tac ctxt
    THEN' (K all_tac APPEND' (fn i => solve_Rel_nat_tac ctxt i)))

fun simp_lhs_solve_Rel_nat_tac ctxt =
  resolve_tac ctxt [@{thm rewrite_Rel_nat_lhs}]
  THEN' HTIU.SIMPS_TO_UNIF_refl_tac (simp_state_update_val_tac ctxt) ctxt
  THEN' solve_Rel_nat_tac ctxt

fun rewrite_ne_zero_if_Rel_nat_tac ctxt =
  HTIU.subst_first_tac ctxt [@{thm rewrite_ne_zero_if_Rel_nat}]
  THEN' simp_lhs_solve_Rel_nat_tac ctxt

(* tactics for assign, seq, and if that run one step of the program, given the appropriate theorems *)

(*applies a theorem of the form: assumes "?P1 c1" and "?P2 c2" shows "?P (Seq c1 c2)" *)
fun seq_tac seq_thmI ctxt = resolve_tac ctxt [seq_thmI]

(*applies a theorem of the following form and solves the premise:
assumes "s' = (STATE (interp_state st))(k := eval exp s)"
shows "?P (Assign k exp) (STATE (interp_state st))"*)
fun assign_tac assign_thmI ctxt =
  resolve_tac ctxt [assign_thmI]
  (*solve state update assumption*)
  THEN' SUT.STATE_interp_update_eq_STATE_interp_fun_upd (simp_state_update_val_tac ctxt) ctxt

fun call_tac call_thmI solve_side_conditions_tac ctxt correctness =
  resolve_tac ctxt [call_thmI]
  THEN' (resolve_tac ctxt correctness
    (*solve correctness side-conditions*)
    THEN_ALL_NEW (SOLVED' solve_side_conditions_tac))
  (*solve state update assumption*)
  THEN' SUT.STATE_interp_update_eq_STATE_interp_fun_upd (simp_state_update_val_tac ctxt) ctxt

(*
assumes "s vb = v"
and "PROP SIMPS_TO_UNIF (v \<noteq> 0) b"
and "b \<Longrightarrow> ?P c c1 s"
and "\<not>b \<Longrightarrow> ?P c c2 s"
shows "?P s (If vb c1 c2)"
*)
fun if_tac if_thmI finish_contradictory_branch ctxt =
  let val SIMP_TO_UNIF_condition_tac = HTIU.SIMPS_TO_UNIF_refl_tac
    (rewrite_ne_zero_if_Rel_nat_tac ctxt) ctxt
  in
    resolve_tac ctxt [if_thmI]
    THEN' SUT.STATE_interp_retrieve_key_eq_tac (HTIU.refl_tac ctxt) ctxt
    THEN' SIMP_TO_UNIF_condition_tac
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
