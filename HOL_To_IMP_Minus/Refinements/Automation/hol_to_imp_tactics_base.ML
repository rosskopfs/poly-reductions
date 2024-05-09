(*  Title:  Refinements/hol_to_imp_tactics_base.ML
    Author: Kevin Kappelmann

Basics to run IMP programs, track their states changes, and prove their
correspondence with HOL programs.
*)
signature HOL_TO_IMP_TACTICS_BASE =
sig
include HAS_LOGGER

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

end

structure HOL_To_IMP_Tactics_Base : HOL_TO_IMP_TACTICS_BASE =
struct

val logger = Logger.setup_new_logger HOL_to_IMP_base_logger "HOL_To_IMP_Tactics_Base"

structure TU = Tactic_Util
structure HTIU = HOL_To_IMP_Util
structure SUT = State_Update_Tracking

structure Seq = HTIU.Seq

fun if_split_tac ctxt =
  split_tac ctxt @{thms if_split}
  THEN_ALL_NEW
    (resolve_tac ctxt @{thms conjI}
    THEN_ALL_NEW resolve_tac ctxt @{thms impI})

fun seq_tac seqE_thms ctxt = eresolve_tac ctxt seqE_thms

fun assign_tac assignD_thms assign_update_simps ctxt = dresolve_tac ctxt assignD_thms
  THEN' SUT.update_state_state_update_tac assign_update_simps ctxt

fun if_tac ifE_thms ctxt = eresolve_tac ctxt ifE_thms
  THEN_ALL_NEW (SUT.rewrite_all_state_retrieval_tac'
    (fn ctxt => HTIU.subst_first_asm_tac ctxt o single) ctxt)

fun run_single_tac assign_tac if_tac more_tacs ctxt =
  FIRST' (map (fn tac => tac ctxt) (more_tacs @ [assign_tac, if_tac]))

fun run_tac seq_tac assign_tac if_tac more_tacs ctxt =
  let val run_single_tac = run_single_tac assign_tac if_tac more_tacs ctxt
  in REPEAT_ALL_NEW (TU.TRY' (seq_tac ctxt) THEN' run_single_tac) end

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

val dest_eq_HOL_term = HTIU.dest_eq #> snd
val dest_eq_HOL_term_prop = HTIU.dest_Trueprop #> dest_eq_HOL_term

fun rewrite_HOL_eq_tac get_HOL_eqs =
  let fun tac ctxt concl = case try (dest_eq_HOL_term_prop #> get_HOL_eqs ctxt) concl of
      SOME (SOME thms) => HTIU.subst_first_tac ctxt thms
    | SOME NONE => (@{log Logger.WARN} ctxt (fn _ => Pretty.block [
        Pretty.str "Could not find HOL equality for HOL term in conclusion ",
        Syntax.pretty_term ctxt concl
      ] |> Pretty.string_of);
      K no_tac)
    | NONE => (@{log Logger.WARN} ctxt (fn _ => Pretty.block [
        Pretty.str "Could not destruct conclusion to find HOL equality ",
        Syntax.pretty_term ctxt concl
      ] |> Pretty.string_of);
      K no_tac)
  in TU.SUBGOAL_STRIPPED (snd o snd) o tac end

fun simp_HOL_def_tac ctxt = asm_full_simp_tac (ctxt addsimps @{thms Let_def})

fun finish_non_induction_tac get_HOL_eqs ctxt =
  SUT.rewrite_all_state_retrieval_tac' (fn ctxt => HTIU.subst_first_tac ctxt o single) ctxt
  THEN' SUT.remove_state_eq_tac ctxt
  THEN' rewrite_HOL_eq_tac get_HOL_eqs ctxt
  THEN_ALL_NEW simp_HOL_def_tac ctxt

(* tactics needed for inductions *)

fun rewrite_insert_current_keys_eq_tac key_terms =
  let open Seq Seq.M
    fun key_eq_focused_tac SIMPS_TO_res {prems=[state_eq_thm], context=ctxt,...} =
      let
        fun rewrite_insert_state_key_eq_tac prems =
          let
            val simp_tac = asm_full_simp_tac (ctxt addsimps prems)
            val state_retrieval_eq_thmsq = SUT.state_retrieval_eq_thmsq simp_tac
              state_eq_thm (apsnd Thm.term_of SIMPS_TO_res) ctxt
            fun rewrite_insert_tac eq_thm = HTIU.subst_first_tac ctxt [eq_thm]
              THEN' Tactic_Util.insert_tac [eq_thm] ctxt
          in
            uncurry state_retrieval_eq_thmsq
            #> map rewrite_insert_tac
            #> flat2
          end
        fun focus_rewrite prems = List.map (rewrite_insert_state_key_eq_tac prems) key_terms
          |> EVERY'
      in TU.FOCUS_PREMS' (focus_rewrite o #prems) ctxt end
    fun current_value_tac ctxt cprems =
      SUT.state_eq_interp_lhs_state_eq_SIMPS_TO_thm_result_state_seq ctxt cprems
      BIND (fn (simps_to_thm, csimps_to, state_eq_prem_index) =>
        TU.focus_prems_tac [state_eq_prem_index + 1]
          (key_eq_focused_tac (simps_to_thm, csimps_to)) ctxt
        |> pure)
      |> flat2
  in TU.CSUBGOAL_STRIPPED (fst o snd) o current_value_tac end

type IMP_keys_retrieval = Proof.context -> term -> term list

fun rewrite_insert_current_keys_eq_tac' get_keys =
  let fun focused_tac ctxt concl =
    let val (hol_term, args) = HTIU.dest_Trueprop concl |> dest_eq_HOL_term |> strip_comb
    in rewrite_insert_current_keys_eq_tac (get_keys ctxt hol_term ~~ args) ctxt end
  in TU.FOCUS_PARAMS_CTXT' (TU.SUBGOAL_STRIPPED (snd o snd) o focused_tac) end

fun finish_induction_tac get_HOL_eqs get_keys ctxt =
  let val finish_goal_tac =
    (*TODO: write a tactic that explicitly applies the inductive hypotheses and
      then simplifies*)
    asm_full_simp_tac ctxt
    THEN_ALL_NEW TU.TRY' (Metis_Tactic.metis_tac [] ATP_Problem_Generate.combsN ctxt [])
  in
    rewrite_HOL_eq_tac get_HOL_eqs ctxt
    THEN' TU.TRY' (simp_HOL_def_tac ctxt)
    THEN' rewrite_insert_current_keys_eq_tac' get_keys ctxt
    THEN' SUT.remove_state_eq_tac ctxt
    THEN_ALL_NEW finish_goal_tac
  end

end
