(*  Title:  Views/IMP/state_update_tracking_imp_tailcalls.ML
    Author: Kevin Kappelmann

Tracking of IMP with tailcalls states changes.
*)
signature STATE_UPDATE_TRACKING_IMP_TAILCALLS =
sig
include HAS_LOGGER

(* big step state utils *)
val dest_IMP_big_step : term -> (term * term) * term * term
val dest_IMP_big_step_prop : term -> (term * term) * term * term

(* initialise state tracking with state from big step premise*)
val init_state_eq_tac: Proof.context -> int -> tactic

(* update state equality following a subprogram call *)
val update_state_call_tac : thm list -> Proof.context -> int -> tactic

end

structure State_Update_Tracking_IMP_Tailcalls : STATE_UPDATE_TRACKING_IMP_TAILCALLS =
struct

val logger = Logger.setup_new_logger HOL_to_IMP_base_logger "State_Update_Tracking_IMP_Tailcalls"

structure HTIU = HOL_To_IMP_Util
structure GU = General_Util
structure TU = Tactic_Util
structure SUT = State_Update_Tracking

(* big step state utils *)
val dest_IMP_big_step =
  \<^Const_fn>\<open>tbig_step_t for _ \<^Const>\<open>Pair _ _ for c s\<close> t s' => \<open>((c, s), t, s')\<close>\<close>
val dest_IMP_big_step_prop = HTIU.dest_Trueprop #> dest_IMP_big_step

val find_IMP_big_step_state_in_prop =
  get_first (try (dest_IMP_big_step o HTIU.dest_Trueprop))
  #> Option.map ((fn ((_, s), _, _) => s))

val init_state_eq_tac =
  let fun tac ctxt prems = case find_IMP_big_step_state_in_prop prems of
      SOME IMP_state => SUT.init_state_eq_tac ctxt (Thm.cterm_of ctxt IMP_state)
    | NONE => (@{log Logger.WARN} ctxt (fn _ => Pretty.block [
          Pretty.str "Could not find IMP big step premise with state in premises ",
          HTIU.pretty_prems ctxt prems
        ] |> Pretty.string_of);
        K no_tac)
  in TU.FOCUS_PARAMS_CTXT' (TU.SUBGOAL_STRIPPED (fst o snd) o tac) end

fun find_update_state_value_eq_prem cupdate_prem cprems =
  let
    val (_, (_, v)) = Thm.term_of cupdate_prem
      |> HTIU.dest_Trueprop |> SUT.dest_update_prem |> snd
    val is_lhs_eq = GU.try_bool
      (Thm.term_of #> HTIU.dest_Trueprop #> HTIU.dest_eq #> fst #> pair v #> (op aconv))
  in GU.find_first_index is_lhs_eq cprems end

open State_Seq_Abbrevs

fun update_state_call_tac update_simps =
  let
    fun insert_new_state_eq_tac interp_state_lhs_state_eq_thm
      {prems=[state_eq_thm, update_thm, update_state_value_eq_thm], context=ctxt,...} =
        SUT.update_state_state_eq_updatesq (update_state_value_eq_thm :: update_simps)
          ctxt state_eq_thm interp_state_lhs_state_eq_thm update_thm
        |> Seq.map (fn thm => TU.insert_tac [thm] ctxt)
        |> Seq_Monad.flat2
    val new_state_eq_tac =
      SUT.state_eq_interp_lhs_state_eq_SIMPS_TO_thm_result_state_seq
      SS_THEN SSS.lift_push_state_monad I (fn (_, cstate_eq_lhs_state) => fn ((_, cprems), ctxt) =>
        SUT.find_cupdate_prem_prop (Thm.term_of cstate_eq_lhs_state) cprems |> Seq.single)
      SS_THEN (fn opt_res => fn sstate as
        (((_, cstate_eq_lhs_state), (_, cprems)), ctxt) => case opt_res of
          SOME (res as (_, cupdate_prem)) =>
            find_update_state_value_eq_prem cupdate_prem cprems
            |> SS.SR.result (SSS.SRS.push res sstate) |> Seq.single
        | NONE => (@{log Logger.WARN} ctxt (fn _ => Pretty.block [
              Pretty.str "Could not find update premise for state ",
              Syntax.pretty_term ctxt (Thm.term_of cstate_eq_lhs_state),
              Pretty.str " in premises ",
              HTIU.pretty_cprems ctxt cprems
            ] |> Pretty.string_of);
            Seq.empty))
      SS_THEN SS.lift_state_single (fn opt_res => fn
        (((update_prem_index, cupdate_prem), ((interp_state_lhs_state_eq_thm, _),
        (state_eq_prem_index, cprems))), ctxt) => case opt_res of
          SOME (update_state_value_eq_prem_index, _) => TU.focus_delete_prems_tac
            (HTIU.successors [state_eq_prem_index, update_prem_index,
              update_state_value_eq_prem_index])
            (insert_new_state_eq_tac interp_state_lhs_state_eq_thm)
            ctxt
        | NONE => (@{log Logger.WARN} ctxt (fn _ => Pretty.block [
              Pretty.str "Could not find equality theorem for value of state update ",
              Syntax.pretty_term ctxt (Thm.term_of cupdate_prem),
              Pretty.str " in premises ",
              HTIU.pretty_cprems ctxt cprems
            ] |> Pretty.string_of);
            K no_tac))
      |> SS.eval #> Seq_Monad.flat2
  in TU.FOCUS_PARAMS_CTXT' (TU.CSUBGOAL_STRIPPED (fst o snd) o (new_state_eq_tac oo SSS.SRS.init)) end


end
