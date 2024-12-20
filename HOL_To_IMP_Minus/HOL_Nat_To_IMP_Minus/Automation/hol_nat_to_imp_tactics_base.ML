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

  val seq_tac : thm -> Proof.context -> int -> tactic
  val assign_tac : thm -> Proof.context -> int -> tactic
  val call_tac : thm -> (int -> tactic) -> Proof.context -> thm list -> int -> tactic
  val if_tac : thm -> Proof.context -> int -> tactic
  val run_step_tac : ('a -> tactic) -> ('a -> tactic) -> ('a -> tactic) -> ('a -> tactic) -> 'a ->
    tactic
  val run_tac : (int -> tactic) -> int -> tactic

  val simp_state_update_val_tac : Proof.context -> int -> tactic

  val transfer_focus_prems_tac : Proof.context -> int -> tactic
  (*reverse transfer; needed when meta variables are on the rhs of the relatedness goal*)
  val rev_transfer_focus_prems_tac : Proof.context -> int -> int -> tactic
  val Rel_nat_condition_tac : Proof.context -> int -> int -> tactic
end

structure HOL_Nat_To_IMP_Tactics_Base : HOL_NAT_TO_IMP_TACTICS_BASE =
struct

val logger = Logger.setup_new_logger HOL_Nat_To_IMP_Minus_base_logger
  "HOL_Nat_To_IMP_Tactics_Base"

structure TU = Tactic_Util
structure SUT = State_Update_Tracking

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

(* tactics for assign, seq, and if that run one step of the program, given the appropriate theorems *)

(*applies a theorem of the form: assumes "?P1 c1" and "?P2 c2" shows "?P (Seq c1 c2)" *)
fun seq_tac seq_thmI ctxt = resolve_tac ctxt [seq_thmI]

fun simp_state_update_val_tac ctxt =
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

(*Rel_nat side condition tactics*)
val transfer_focus_prems_tac = Tactic_Util.FOCUS_PREMS' (fn ({prems, context, ...}) =>
  let val ctxt = context |> Context.Proof
    |> fold (Thm.attribute_declaration Transfer.transfer_add) prems
    |> Context.proof_of
  in Transfer.transfer_prover_tac ctxt end)

fun rev_transfer_focus_prems_tac ctxt vari i = Tactical.PRIMSEQ (fn state =>
  let (*do not use Tactic_Util.FOCUS_PREMS' directily as it fixes schematic types in the conclusion*)
    val ({prems, context, concl, ...}, _) = Subgoal.focus_prems ctxt i NONE state
    (* add prems as transfer rules *)
    val ctxt' = fold (Thm.attribute_declaration Transfer.transfer_add) prems (Context.Proof context)
      |> Context.proof_of
    (*get the term we need to find a partner for*)
    val lhsct = concl |> Thm.dest_arg |> Thm.dest_arg1
    (*abuse a theorem to get the partner*)
    val inst_thm = Drule.infer_instantiate' ctxt' [SOME lhsct] @{thm "transfer_inst"}
    val thm' = Thm.apply_attribute (Transfer.transferred_attribute []) inst_thm (Context.Proof ctxt')
      |> fst |> Thm.varifyT_global |> Drule.incr_indexes state
    (*retrieve the partner*)
    val rhsct = Thm.cprems_of thm' |> hd |> Thm.dest_arg |> Thm.dest_arg1
    (*plug in in the result*)
    val inst_tac = Drule.infer_instantiate' ctxt (replicate (vari - 1) NONE @ [SOME rhsct])
      |> Tactical.PRIMITIVE
  in (inst_tac THEN transfer_focus_prems_tac ctxt i) state end)

fun Rel_nat_condition_tac ctxt vari =
  resolve_tac ctxt [@{thm rewrite_Rel_nat_lhs}]
  THEN' simp_state_update_val_tac ctxt
  THEN' rev_transfer_focus_prems_tac ctxt vari

end
