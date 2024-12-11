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

  val seq_tac: thm -> Proof.context -> int -> tactic
  val assign_tac: thm -> Proof.context -> int -> tactic
  val call_tac: thm -> (int -> tactic) -> Proof.context -> thm list -> int -> tactic
  val if_tac: thm -> Proof.context -> int -> tactic
  val run_step_tac: ('a -> tactic) -> ('a -> tactic) -> ('a -> tactic) -> ('a -> tactic) -> 'a -> tactic
  val run_tac: (int -> tactic) -> int -> tactic

  val simp_update_tac: Proof.context -> int -> tactic

  val transfer_foc_tac : Proof.context -> int -> tactic
  val transfer_foc_rev_tac : Proof.context -> int -> int -> tactic
  val rel_condition_tac : Proof.context -> int -> int -> tactic
end

structure HOL_Nat_To_IMP_Tactics_Base : HOL_NAT_TO_IMP_TACTICS_BASE =
struct

val logger = Logger.setup_new_logger HOL_Nat_To_IMP_Minus_base_logger
  "HOL_Nat_To_IMP_Tactics_Base"

structure TU = Tactic_Util
structure SUT = State_Update_Tracking

fun transfer_foc_tac ctxt = Tactic_Util.FOCUS_PREMS' (fn ({prems, context, ...}) =>
  let
    val ctxt' = fold (snd oo Thm.apply_attribute Transfer.transfer_add) prems (Context.Proof context)
      |> Context.proof_of
  in
    (Transfer.transfer_prover_tac ctxt')
  end) ctxt

fun transfer_foc_rev_tac ctxt vari i = Tactical.PRIMSEQ (fn state =>
  let (* Do not use Tactic_Util.FOCUS_PREMS' directily as it fixes schematic types in the conclusion *)
    val ({prems, context, concl, ...}, _) = Subgoal.focus_prems ctxt i NONE state
    (* Add prems as transfer rules *)
    val ctxt' = fold (snd oo Thm.apply_attribute Transfer.transfer_add) prems (Context.Proof context)
      |> Context.proof_of
    (* Get element we need to find relation for *)
    val lhsct = concl |> Thm.dest_arg |> Thm.dest_arg1
    (* Instantiate transfer_inst *)
    val inst_thm = @{thm "transfer_inst"} |> Drule.infer_instantiate' ctxt' [SOME lhsct]
    (* Abuse alternative form to get transferred form *)
    val thm' = Thm.apply_attribute (Transfer.transferred_attribute []) inst_thm (Context.Proof ctxt') |> fst
      |> Thm.varifyT_global |> Drule.incr_indexes state
    (* Select transferred result *)
    val rhsct = Thm.cprems_of thm' |> hd |> Thm.dest_arg |> Thm.dest_arg1
    (* Plugin in the result *)
    val inst_tac = Drule.infer_instantiate' ctxt (replicate (vari-1) NONE @ [SOME rhsct]) |> Tactical.PRIMITIVE
  in
    (inst_tac THEN transfer_foc_tac ctxt i) state
  end)

fun rel_condition_tac ctxt vari =
  resolve_tac ctxt @{thms Rel_nat_rewrite_lhs}
  THEN' SUT.STATE_interp_retrieve_key_eq_tac (simp_tac ctxt) ctxt
  THEN' transfer_foc_rev_tac ctxt vari

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

fun call_tac call_thmI solve_sideconditions_tac ctxt correctness =
  resolve_tac ctxt [call_thmI]
  (*solve correctness assumption*)
  THEN' (resolve_tac ctxt correctness THEN_ALL_NEW (SOLVED' solve_sideconditions_tac))
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
    THEN' SUT.STATE_interp_retrieve_key_eq_tac (HOL_Nat_To_IMP_Util.refl_tac ctxt) ctxt
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
