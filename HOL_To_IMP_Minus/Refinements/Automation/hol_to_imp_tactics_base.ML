(*  Title:  Refinements/hol_to_imp_tactics_base.ML
    Author: Kevin Kappelmann

Basics to run IMP programs, track their states changes, and prove their
correspondence with HOL programs.
*)
signature HOL_TO_IMP_TACTICS_BASE =
sig
include HAS_LOGGER

(*
val if_split_tac: Proof.context -> int -> tactic

val seq_tac : thm list -> Proof.context -> int -> tactic
val assign_tac : thm list -> thm list -> Proof.context -> int -> tactic
val if_tac : thm list -> Proof.context -> int -> tactic

val run_single_tac : ('a -> 'b -> tactic) -> ('a -> 'b -> tactic) -> ('a -> 'b -> tactic) list ->
  'a -> 'b -> tactic
val run_tac : ('a -> int -> tactic) -> ('a -> int -> tactic) -> ('a -> int -> tactic) ->
  ('a -> int -> tactic) list -> 'a -> int -> tactic

(*retrieve HOL equalities from HOL term (including possible arguments)*)
type HOL_eqs_retrieval = Proof.context -> term -> thm list option
val get_HOL_eqs : HOL_eqs_retrieval

val dest_eq_HOL_term : term -> term
val dest_eq_HOL_term_prop : term -> term

val rewrite_HOL_eq_tac : HOL_eqs_retrieval -> Proof.context -> int -> tactic

val simp_HOL_def_tac : Proof.context -> int -> tactic

val finish_non_induction_tac : HOL_eqs_retrieval -> Proof.context -> int -> tactic

val rewrite_insert_current_keys_eq_tac : (term * term) list -> Proof.context -> int -> tactic

(*retrieve keys of IMP program corresponding to arguments of a given HOL term*)
type IMP_keys_retrieval = Proof.context -> term -> term list
val rewrite_insert_current_keys_eq_tac': IMP_keys_retrieval -> Proof.context -> int -> tactic

val finish_induction_tac : HOL_eqs_retrieval -> IMP_keys_retrieval -> Proof.context -> int -> tactic
*)

end

structure HOL_To_IMP_Tactics_Base (* : HOL_TO_IMP_TACTICS_BASE *) =
struct

val logger = Logger.setup_new_logger HOL_to_IMP_base_logger "HOL_To_IMP_Tactics_Base"

structure HTIU = HOL_To_IMP_Util
structure TU = Tactic_Util


fun simpset_only ctxt thms = Simplifier.put_simpset HOL_basic_ss ctxt addsimps thms


(* find theorems of the form "f x = ...", given f possibly applied to some arguments *)
type HOL_eqs_retrieval = Proof.context -> term -> thm list option
(* FIXME: create a more robust filter *)
fun get_HOL_eqs ctxt t =
  let val thms = Find_Theorems.find_theorems ctxt NONE NONE true [
      (* search for the head constant *)
      (true, Find_Theorems.Pattern (head_of t)),
      (* ignore conditional rules *)
      (false, Find_Theorems.Pattern @{term "(\<Longrightarrow>)"})
    ] |> snd |> map snd
  in if null thms then NONE else SOME thms end

fun SIMPS_TO_tac simps ctxt =
  TU.TRY' (simp_tac (ctxt addsimps simps))
  THEN' resolve_tac ctxt [@{thm SIMPS_TOI}]

fun SIMPS_TO_UNIF_tac' simp_tac ctxt =
  resolve_tac ctxt [@{thm SIMPS_TO_UNIFI}]
    (* #> HTIU.time_tac Pretty.writeln "SIMPS_TO_UNIF/resolve_tac(1)" *)
  THEN' ((* TU.TRY' *) simp_tac
    (* #> HTIU.time_tac Pretty.writeln "SIMPS_TO_UNIF/SIMPS_TO" *) )
  THEN' resolve_tac ctxt [@{thm SIMPS_TOI}]
  THEN' (resolve_tac ctxt [@{thm reflexive}] (* ? *)
    (* #> HTIU.time_tac Pretty.writeln "SIMPS_TO_UNIF/resolve_tac(2)" *) )

(* helpers for updating and retrieving protected STATEs *)

val STATE_interp_state_State_thms = @{thms STATE_eq interp_state_State_eq}

(* fun SIMPS_TO_UNIF_STATE_interp_state_State_tac ctxt = *)
  (* SIMPS_TO_UNIF_tac STATE_interp_state_State_thms ctxt *)
  (* #> HTIU.time_tac Pretty.writeln "SIMPS_TO_UNIF" *)

fun simp_lookups_tac ctxt =
  TU.TRY' (Simplifier.simp_tac (simpset_only ctxt @{thms retrieval_simps}))

fun STATE_interp_lookup_tac ctxt simp_thms =
  SIMPS_TO_UNIF_tac' (
      TU.TRY' (Simplifier.simp_tac (simpset_only ctxt simp_thms))
      THEN' simp_lookups_tac ctxt
      (* unconstrained simplification: probably unavoidable here *)
      THEN' TU.TRY' (Simplifier.asm_simp_tac ctxt)
    ) ctxt

fun STATE_interp_update_fun_upd ctxt simp_thms =
  resolve_tac ctxt [@{thm trans}] (* for norm_state *)
  THEN' resolve_tac ctxt [@{thm STATE_interp_update_eq_STATE_interp_fun_updI_2}]
  THEN' STATE_interp_lookup_tac ctxt simp_thms
  THEN' resolve_tac ctxt @{thms refl} (* alternatively: norm_state *)

(* TODO: what to do before/after simp_lookups_tac in STATE_interp_lookup_tac *)
fun STATE_interp_retrieve_key_tac simp_thms ctxt =
  resolve_tac ctxt [@{thm STATE_interp_retrieve_key_eqI_2}]
  THEN' STATE_interp_lookup_tac ctxt simp_thms
  (* THEN' finish_eq_tac *)

(* tactics for assign, seq, and if that run one step of the program, given the appropriate theorems *)

fun assign_tac thms simp_thms ctxt =
  resolve_tac ctxt thms
  THEN' STATE_interp_update_fun_upd ctxt simp_thms
  (* #> HTIU.time_tac Pretty.writeln "assign_tac" *)

fun seq_tac thms ctxt = resolve_tac ctxt thms
  (* #> HTIU.time_tac Pretty.writeln "seq_tac" *)

fun if_tac thms ctxt =
  resolve_tac ctxt thms
  THEN' SIMPS_TO_UNIF_tac' (simp_lookups_tac ctxt) ctxt
  THEN' SIMPS_TO_UNIF_tac' (TU.TRY' (Simplifier.asm_simp_tac ctxt)) ctxt
  THEN' SIMPS_TO_UNIF_tac' (TU.TRY' (Simplifier.asm_simp_tac ctxt)) ctxt
  (* #> HTIU.time_tac Pretty.writeln "if_tac" *)

fun call_tac thms simp_thms ctxt correctness =
  resolve_tac ctxt thms
  (* solve correctness assumption *)
  THEN' resolve_tac ctxt correctness
  (* solve state update assumption: s' = s(r := val) *)
  THEN' STATE_interp_update_fun_upd ctxt simp_thms
  (* #> HTIU.time_tac Pretty.writeln "call_tac" *)

(* run one (seq assign ...), (seq call ...), or if step of a program *)
fun run_step_tac seq_tac assign_tac call_tac if_tac =
  ((seq_tac THEN' (assign_tac ORELSE' call_tac))
    ORELSE' if_tac)
   (* #> HTIU.time_tac Pretty.writeln "run_step_tac" *)

(* usage: run_tac (run_step_tac ...) *)
val run_tac = TU.TRY' o REPEAT_ALL_NEW

end
