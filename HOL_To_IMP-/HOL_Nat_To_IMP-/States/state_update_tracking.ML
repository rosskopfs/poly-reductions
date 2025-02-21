(*  Title:  States/state_update_tracking.ML
    Author: Kevin Kappelmann

Tracking of STATE equalities.
*)
signature STATE_UPDATE_TRACKING =
sig
  include HAS_LOGGER

  val dest_STATE : term -> term
  val cdest_STATE : cterm -> cterm

  (*state retrieval utils*)
  val mk_state_retrieval : term -> term -> term
  val dest_state_retrieval : term -> term * term
  val is_state_state_retrieval : term -> term -> bool

  val simp_STATE_interp_retrieve_key : (Proof.context -> int -> tactic) -> Proof.context ->
    int -> tactic

  val STATE_interp_retrieve_key_eq_tac : (int -> tactic) -> Proof.context -> int -> tactic
  val STATE_interp_update_eq_STATE_interp_fun_upd : (int -> tactic) -> Proof.context -> int -> tactic
end

structure State_Update_Tracking : STATE_UPDATE_TRACKING =
struct
structure HTIU = HOL_Nat_To_IMP_Util
val logger = Logger.setup_new_logger Logger.root "State_Update_Tracking"

val state_eq = curry (op aconv)

(* state equality utils *)
val dest_STATE = \<^Const_fn>\<open>STATE _ for s => s\<close>
val cdest_STATE = Thm.dest_arg

(* state retrieval utils *)
fun mk_state_retrieval state key = state $ key
val dest_state_retrieval = Term.dest_comb
fun is_state_state_retrieval state s_app = dest_state_retrieval s_app |> fst |> state_eq state

fun string_eq ctxt ct =
  let val cps = Thm.dest_binop ct
  in
    case apply2 (Thm.term_of #> try HOLogic.dest_string) cps of
      (NONE, _) => NONE
    | (_, NONE) => NONE
    | (SOME s1, SOME s2) => if s1 = s2
      then SOME (Thm.instantiate'[] [SOME (fst cps)] @{thm string_eq_eq_True})
      else Nbe.dynamic_conv ctxt ct |> SOME
  end

val string_eq_congroc =
  \<^simproc_setup>\<open>passive congproc string_eq ("(s :: string) = s'") =
    \<open>K string_eq\<close>\<close>

fun simp_STATE_interp_retrieve_key simp_tac ctxt =
  let
    val ctxt = Simplifier.add_proc string_eq_congroc ctxt
    val ctxt = ctxt addsimps
      @{thms STATE_interp_update_retrieve_key_eq_if STATE_interp_state_state_eq}
  in simp_tac ctxt end

fun STATE_interp_retrieve_key_eq_tac finish_eq_tac ctxt =
  resolve_tac ctxt [@{thm STATE_interp_retrieve_key_eqI}]
  THEN' HTIU.SIMPS_TO_UNIF_refl_tac (simp_STATE_interp_retrieve_key safe_simp_tac ctxt) ctxt
  THEN' finish_eq_tac

(* fun simp_state_tac ctxt = safe_simp_tac
  (ctxt addsimps @{thms update_state_def state_def}) *)

fun timed' tac_name (tac : int -> tactic) ctxt i state =
  case Logger.lookup_logger logger (Context.Proof ctxt) of
    NONE => tac i state
  | SOME {log_level,...} => if Logger.DEBUG <= log_level
      then
        let
          val _ = @{log Logger.DEBUG} ctxt (fn _ => "Running " ^ tac_name)
          fun pull sq = Seq.pull sq |> (fn r => Seq.make (K r))
          val (timing, res) = Timing.timing (tac i #> pull) state
          val _ = @{log Logger.DEBUG} ctxt
            (fn _ => "Done with " ^ tac_name ^ ".\nTime: " ^ Timing.message timing)
        in res end
      else tac i state

fun STATE_interp_update_eq_STATE_interp_fun_upd simp_tac ctxt =
  resolve_tac ctxt [@{thm STATE_interp_update_eq_STATE_interp_fun_updI}]
  THEN' timed' "state retrieval" (HTIU.SIMPS_TO_UNIF_refl_tac simp_tac ctxt) ctxt
  (*FIXME: updates of a TRIE state cannot be normalised by evaluation and normalising it with the
  simplifier is too slow; hence, we postpone the construction of the state until we do a lookup.
  This, however, means that each lookup has to re-create the tree structure. Still, doing so by
  normalisation is quicker than updating the tree with the simplifier*)
  (* THEN' timed' "update" (HTIU.SIMPS_TO_UNIF_refl_tac (simp_state_tac ctxt) ctxt) ctxt *)
  THEN' timed' "state update" (HTIU.SIMPS_TO_UNIF_refl_tac (K all_tac) ctxt) ctxt

end
