(*  Title:  Automation/hol_nat_to_imp_tailcalls_tactics.ML
    Author: Kevin Kappelmann
    Author: Max Lang

Tactics to run IMP-Tailcall programs, track their states changes, and prove their
correspondence with HOL programs.
*)
signature HOL_NAT_TO_IMP_TAILCALLS_TACTICS =
sig
  include HAS_LOGGER
  type IMP_def_retrieval = Proof.context -> term -> thm option
  val get_IMP_def: IMP_def_retrieval

  type imp_correct_retrieval = Proof.context -> term -> thm list option
  val get_imp_correct: Proof.context -> Termtab.key -> thm list option

  type fun_inducts_retrieval = Proof.context -> term -> thm list option
  val get_fun_inducts: fun_inducts_retrieval

  type terminates_with_IMP_Tailcall_args = {c: term, s: term, s': term, tc: term}
  type terminates_with_res_IMP_Tailcall_args = {c: term, r: term, s: term, tc: term, v: term}

  val dest_terminates_with_res_IMP_Tailcall : term -> terminates_with_res_IMP_Tailcall_args
  val dest_terminates_with_res_IMP_Tailcall_prop : term -> terminates_with_res_IMP_Tailcall_args
  val dest_terminates_with_IMP_Tailcall : term -> terminates_with_IMP_Tailcall_args
  val dest_terminates_with_IMP_Tailcall_prop : term -> terminates_with_IMP_Tailcall_args
  val with_dest_terminates_with_res_IMP_Tailcall_prop : Proof.context ->
      (terminates_with_res_IMP_Tailcall_args -> int -> tactic) -> int -> tactic

  val rewrite_eq_state_retrieval_sym_tac : Proof.context -> int -> tactic
  val setup_induction_tac : fun_inducts_retrieval -> Proof.context -> int -> tactic

  val start_case_tac : IMP_def_retrieval -> Proof.context -> int -> tactic

  val terminates_with_res_tSeq_tac : Proof.context -> int -> tactic

  val terminates_with_res_tAssign_tac : Proof.context -> int -> tactic
  val terminates_with_tAssign_tac : Proof.context -> int -> tactic

  val terminates_with_tCall_tac : fun_inducts_retrieval -> Proof.context -> int -> tactic

  val delete_IH_prems : int -> tactic

  val finish_contradictory_branch : Proof.context -> int -> tactic
  val SIMPS_TO_if_assumption_tac : Proof.context -> int -> tactic
  val SIMPS_TO_if_assumption_loop : string * (Proof.context -> int -> tactic)
  val add_SIMPS_TO_if_assumption_loop : Context.generic -> Context.generic
  val terminates_with_res_tIf_tac : Proof.context -> int -> tactic

  val run_step_tac : imp_correct_retrieval -> Proof.context -> int -> tactic
  val run_tac : imp_correct_retrieval -> Proof.context -> int -> tactic

  val subst_HOL_fun_eq_tac : thm list -> Proof.context -> int -> tactic

  val finish_non_tail_tac : Proof.context -> int -> tactic
  val apply_IH_tac : Proof.context -> int -> tactic
  val solve_IH_prem_tac : Proof.context -> int -> tactic
  val finish_tail_tac : Proof.context -> int -> tactic

  val run_HOL_fun_tac : HOL_Nat_To_IMP_Tactics_Gen.HOL_eqs_retrieval -> Proof.context -> int -> tactic
  val finish_tac : HOL_Nat_To_IMP_Tactics_Gen.HOL_eqs_retrieval -> Proof.context -> int -> tactic

  val start_run_finish_case_tac : IMP_def_retrieval -> imp_correct_retrieval ->
    HOL_Nat_To_IMP_Tactics_Gen.HOL_eqs_retrieval -> Proof.context -> int -> tactic

  val start_run_finish_tac : bool -> fun_inducts_retrieval -> IMP_def_retrieval ->
    imp_correct_retrieval -> HOL_Nat_To_IMP_Tactics_Gen.HOL_eqs_retrieval -> Proof.context ->
    int -> tactic
end

structure HOL_Nat_To_IMP_Tailcalls_Tactics : HOL_NAT_TO_IMP_TAILCALLS_TACTICS =
struct

val logger =
  Logger.setup_new_logger HOL_Nat_To_IMP_Tactics_Gen.logger "HOL_Nat_To_IMP_Tailcalls_Tactics"

structure HTITG = HOL_Nat_To_IMP_Tactics_Gen
structure GU = General_Util
structure TU = Tactic_Util
structure HTIU = HOL_Nat_To_IMP_Util
structure SUT = State_Update_Tracking

structure Seq = HTIU.Seq
structure List = HTIU.List

type IMP_def_retrieval = Proof.context -> term -> thm option
val get_IMP_def = Compile_HOL_Nat_To_IMP.get_compiled_const_def

type imp_correct_retrieval = Proof.context -> term -> thm list option
val get_imp_correct =
  Option.map single oo HOL_Nat_To_IMP_Goal_Command.get_imp_correct

(*retrieve induction rule for HOL function*)
type fun_inducts_retrieval = Proof.context -> term -> (thm list) option
fun get_fun_inducts ctxt t = HOL_Fun_To_HOL_Nat_Fun.get_compiled_related_HOL ctxt t
  |> the_default t
  |> try (Function.get_info ctxt #> #inducts) |> Option.join

(*destructors for IMP-Tailcalls*)
type terminates_with_res_IMP_Tailcall_args = {tc: term, c: term, s: term, r: term, v: term}
type terminates_with_IMP_Tailcall_args = {tc: term, c: term, s: term, s': term}

val dest_terminates_with_res_IMP_Tailcall =
  \<^Const_fn>\<open>terminates_with_res_IMP_Tailcall for tc c s r v =>
    \<open>{tc = tc, c = c, s = s, r = r, v = v}\<close>\<close>
val dest_terminates_with_res_IMP_Tailcall_prop =
  HTIU.dest_Trueprop #> dest_terminates_with_res_IMP_Tailcall

val dest_terminates_with_IMP_Tailcall =
  \<^Const_fn>\<open>terminates_with_IMP_Tailcall for tc c s s' => \<open>{tc = tc, c = c, s = s, s' = s'}\<close>\<close>
val dest_terminates_with_IMP_Tailcall_prop =
  HTIU.dest_Trueprop #> dest_terminates_with_IMP_Tailcall

fun with_dest_terminates_with_res_IMP_Tailcall_prop ctxt = HTIU.with_dest_concl_tac (fn _ => Pretty.block [
    Pretty.str "Could not find ",
    Syntax.pretty_term ctxt @{term terminates_with_res_IMP_Tailcall},
    Pretty.str " in conclusion."
  ] |> Pretty.string_of)
  dest_terminates_with_res_IMP_Tailcall_prop ctxt

fun with_dest_terminates_with_IMP_Tailcall_prop ctxt = HTIU.with_dest_concl_tac (fn _ => Pretty.block [
    Pretty.str "Could not find ",
    Syntax.pretty_term ctxt @{term terminates_with_IMP_Tailcall},
    Pretty.str " in conclusion."
  ] |> Pretty.string_of)
  dest_terminates_with_IMP_Tailcall_prop ctxt

(* starting tactics *)
val rewrite_eq_state_retrieval_sym_tac =
  let
    fun rewrite_focused_tac {prems, context = ctxt,...} =
      let val prems_flipped = map (HTIU.flip_eq_thm ctxt) prems
      in
        HTIU.simp_only_tac ctxt prems_flipped
        THEN' TU.insert_tac prems_flipped ctxt
      end
    fun rewrite_tac ctxt prems {s,...}  =
      let
        val is_eq_state_retrieval_prem = GU.try_bool
          (HTIU.dest_Trueprop #> HTIU.dest_eq #> snd #> SUT.is_state_state_retrieval s)
        val eq_state_retrieval_prems = GU.find_indices is_eq_state_retrieval_prem prems
      in
        TU.focus_delete_prems_tac (HTIU.successors eq_state_retrieval_prems)
          rewrite_focused_tac ctxt
      end
  in
    TU.FOCUS_PARAMS_CTXT' (TU.SUBGOAL_STRIPPED (fst o snd) o
      (fn ctxt => with_dest_terminates_with_res_IMP_Tailcall_prop ctxt o rewrite_tac ctxt))
  end

fun setup_induction_tac get_fun_inducts =
  let fun focused_tac {context = ctxt, ...} {s, v,...} prems =
    let
      val head = head_of v
      val instantiations = prems
        |> map_filter (try (HTIU.dest_Trueprop #> HOL_To_HOL_Nat_Util.dest_Rel_nat))
        |> (fn
            (*instantiations if there are no Rel_nat premises*)
            [] => Compile_HOL_Nat_To_IMP.get_compiled_const ctxt head |> #arg_regs
              |> map (HTIU.mk_state_register_retrieval s)
            (*instantiations if there are Rel_nat premises*)
          | xs => map (snd #> snd) xs)
        |> map (fn t => SOME (NONE, (t, false)))
      val arbitrary = [dest_Free s]
      val inducts = get_fun_inducts ctxt head
    in
      Induction.induction_tac ctxt true [instantiations] [arbitrary] [] inducts []
      (*needed for inductions of functions defined on pattern matching; they create equalities of the
         form "t = s ''<register>''", which have to be rewritten in the goal's conclusion"*)
      THEN_ALL_NEW (TRY o rewrite_eq_state_retrieval_sym_tac ctxt)
    end
  in
    TU.FOCUS_PARAMS' (fn focus as {context = ctxt,...} =>
      with_dest_terminates_with_res_IMP_Tailcall_prop ctxt
      (TU.SUBGOAL_STRIPPED (fst o snd) o focused_tac focus))
  end

fun start_case_tac get_IMP_def ctxt =
  let fun tac {c,...} =
    (*unfold the definition of the IMP program at the right position*)
    EqSubst.eqsubst_tac ctxt [2] (get_IMP_def ctxt c |> the_list)
    THEN' resolve_tac ctxt [@{thm terminates_with_res_IMP_Tailcall_start}]
  in with_dest_terminates_with_res_IMP_Tailcall_prop ctxt tac end

(* tactics for tAssign, tSeq, and tIf that run one step of the tailcall program *)

val terminates_with_res_tSeq_tac = HTITG.seq_tac @{thm terminates_with_res_tSeqI}

val terminates_with_res_tAssign_tac = HTITG.assign_tac @{thm terminates_with_res_tAssignI}
val terminates_with_tAssign_tac = HTITG.assign_tac @{thm terminates_with_tAssignI}

val is_ih = can (Term_Util.strip_subgoal #> snd #> snd #> dest_terminates_with_res_IMP_Tailcall_prop)

val delete_IH_prems =
  let fun tac prems i state =
    let val ih_prems = fold_index (fn (i, prem) => if is_ih prem then cons (i + 1) else I) prems []
    in TU.thin_tacs ih_prems i state end
  in TU.SUBGOAL_STRIPPED (snd #> fst) tac end

fun terminates_with_tCall_tac get_imp_correct ctxt =
  let fun tac {c,...} = case c of
      \<^Const_>\<open>tCall for c _\<close> => (case get_imp_correct ctxt c of
          NONE => (@{log Logger.WARN} ctxt (fn _ => Pretty.block [
              Pretty.str "Could not find correctness theorem for ",
              Syntax.pretty_term ctxt c
            ] |> Pretty.string_of);
            K no_tac)
        | SOME cs => HTITG.call_tac @{thm terminates_with_tCallI}
            (delete_IH_prems THEN' HTITG.simp_lhs_solve_Rel_nat_tac ctxt) ctxt cs)
    | _ => K no_tac
  in with_dest_terminates_with_IMP_Tailcall_prop ctxt tac end

fun finish_contradictory_branch ctxt =
  (delete_IH_prems
  THEN' safe_asm_full_simp_tac (ctxt addsimps HTITG.get_HOL_To_IMP_finish_simps ctxt))
  |> SOLVED'

(*SIMPS_TO looper needed for if conditions containing meta variables*)
fun SIMPS_TO_if_assumption_tac ctxt =
  resolve_tac ctxt @{thms SIMPS_TO_if_TrueI SIMPS_TO_if_FalseI}
  THEN' assume_tac ctxt
val SIMPS_TO_if_assumption_loop = ("SIMPS_TO_if_assumption", SIMPS_TO_if_assumption_tac)
val add_SIMPS_TO_if_assumption_loop = Simplifier.map_ss
  (fn ctxt => ctxt addloop SIMPS_TO_if_assumption_loop)

fun terminates_with_res_tIf_tac ctxt =
  HTITG.if_tac @{thm terminates_with_res_tIf_processedI} (finish_contradictory_branch ctxt) ctxt

fun run_step_tac get_imp_correct ctxt = HTITG.run_step_tac
  (terminates_with_res_tSeq_tac ctxt)
  (terminates_with_tAssign_tac ctxt)
  (terminates_with_tCall_tac get_imp_correct ctxt)
  (terminates_with_res_tIf_tac ctxt)

(*run a tailcall program to completion, ends with
terminates_with_res _ c _ _ _, where c is either an assignment or tTAIL *)
fun run_tac get_imp_correct = HTITG.run_tac o run_step_tac get_imp_correct

(* finishing tactics *)

fun apply_IH_tac ctxt =
  let open Seq.M open HTIU.Let
    (*get a list of theorems of the form t_i = s ''reg_i'',
    one for each argument in the function application term v*)
    fun get_reg_eq_thms ctxt arg_reg_eq_tac s v =
      (*v is of the form f t1 t2 ..., where f is the relevant HOL function; extract the head f,
      and the terms t1, t2, ... *)
      Term.strip_comb v
        ||> filter (Term.fastype_of #> HOL_To_HOL_Nat_Util.is_itself #> not)
      LET (fn (head, arg_terms) =>
        (* fetch the compiled constant *)
        Basics.try (Compile_HOL_Nat_To_IMP.get_compiled_const ctxt) head
        |> HTIU.seq_of_opt (fn _ => @{log Logger.WARN} ctxt (fn _ => Pretty.block [
            Pretty.str "Could not load compiled constant for ",
            Syntax.pretty_term ctxt head
          ] |> Pretty.string_of))
      (* construct equalities of the form t_i = s ''reg_i'' *)
      >>= (fn {arg_regs,...} => map2 (fn t => fn reg =>
        HTIU.mk_eq (t, HTIU.mk_state_register_retrieval s reg)
        |> HTIU.mk_Trueprop |> Thm.cterm_of ctxt)
        arg_terms arg_regs
      LET (fn arg_reg_eqs => arg_reg_eqs
        (*prove the equalities*)
        |> List.map (TU.HEADGOAL (TU.apply_tac (SOLVED' arg_reg_eq_tac))) |> List.T_Seq.sequence
        (*TODO: show the user which equality could not be proven*)
        |> HTIU.seq_peek_empty (fn _ => @{log Logger.DEBUG} ctxt (fn _ => Pretty.block [
              Pretty.str "Could not prove one or more of the register equalities: ",
              Pretty.block (List.map (Thm.term_of #> Syntax.pretty_term ctxt) arg_reg_eqs)
            ] |> Pretty.string_of))
      )))
    (*tactic for proving the equalities*)
    fun arg_reg_eq_tac ctxt prems =
      resolve_tac ctxt [@{thm sym}]
      THEN' SUT.STATE_interp_retrieve_key_eq_tac (safe_simp_tac (ctxt addsimps prems)) ctxt
    (* rewrite each argument t_i to s ''reg_i'' *)
    fun rewrite_conclusion_arguments_tac ctxt arg_reg_eq_thms =
      let
        (* each argument is first drawn out into a separate subgoal t_i = ?v s
           to prevent substitution from occurring inside s *)
        fun rewrite_args_tac [] = HTIU.SIMPS_TO_UNIF_refl_tac (K all_tac) ctxt
          | rewrite_args_tac (thm :: thms) =
              (*splitting the arguments needs a special unifier*)
              Unify_Resolve_Base.unify_resolve_tac
                (HOL_To_IMP_Unification.norms_first_higherp_decomp_comb_higher_unify)
                (HOL_To_IMP_Unification.first_higherp_decomp_comb_higher_unify)
                @{thm SIMPS_TO_UNIF_SIMPS_TO_UNIF_cong} ctxt
              THEN' rewrite_args_tac thms
              THEN' Simps_To_Unif.SIMPS_TO_UNIF_tac (K all_tac)
                (resolve_tac ctxt [thm COMP_INCR @{thm eq_reflection}]) ~1 ctxt
      in
        resolve_tac ctxt [@{thm rewrite_terminates_with_res_IMP_Tailcall_value}]
        THEN' rewrite_args_tac (rev arg_reg_eq_thms)
      end
    fun apply_with_IH_tac ctxt prems s arg_reg_eq_thms =
      let
        val s_ct = Thm.cterm_of ctxt s
        val s_typ = Thm.typ_of_cterm s_ct
        (*induction hypotheses can have multiple free variables - find all of them that could be
        the state*)
        val inst_vars = Thm.prop_of
          #> (fn t => Term.add_vars t [])
          #> List.filter (fn (_, typ) => typ = s_typ)
          #> rev (*right state is probably at the front*)
        val is_ih = Thm.prop_of #> is_ih
        val instantiate_apply_ih_tac = filter is_ih prems |> Seq.of_list
          >>= (fn ih => inst_vars ih |> Seq.of_list
          >>= (fn inst_var => Thm.instantiate (TVars.empty, Vars.make1 (inst_var, s_ct)) ih |> pure
          >>= (fn ih_inst => resolve_tac ctxt [ih_inst] |> pure)))
          |> flat2
        val prepare_ih_prem_goal_tac =
          safe_simp_tac (fold (Raw_Simplifier.flip_simp) arg_reg_eq_thms (clear_simpset ctxt))
      in instantiate_apply_ih_tac THEN_ALL_NEW prepare_ih_prem_goal_tac end
    fun prems_tac {context = ctxt, prems,...} {s, v,...} =
      get_reg_eq_thms ctxt (arg_reg_eq_tac ctxt prems) s v
      >>= (fn arg_reg_eq_thms =>
        rewrite_conclusion_arguments_tac ctxt arg_reg_eq_thms
        THEN' apply_with_IH_tac ctxt prems s arg_reg_eq_thms
        |> pure)
      |> flat2
  in
    resolve_tac ctxt [@{thm terminates_with_res_tTailI}]
    THEN' TU.FOCUS_PREMS' (fn focus => with_dest_terminates_with_res_IMP_Tailcall_prop
      (#context focus) (prems_tac focus)) ctxt
  end

fun solve_IH_prem_tac ctxt =
  delete_IH_prems
  THEN' TRY o safe_asm_full_simp_tac ctxt
  THEN_ALL_NEW TRY o HTITG.solve_Rel_nat_tac ctxt

fun finish_tail_tac ctxt =
  apply_IH_tac ctxt
  THEN_ALL_NEW solve_IH_prem_tac ctxt

fun finish_non_tail_tac ctxt =
  terminates_with_res_tAssign_tac ctxt
  THEN' delete_IH_prems
  THEN' SUT.STATE_interp_retrieve_key_eq_tac
    (asm_full_simp_tac (ctxt addsimps HTITG.get_HOL_To_IMP_finish_simps ctxt)) ctxt

(*shared tail/non-tail finish tactics*)
fun simp_res_value_tac simp_tac ctxt =
  resolve_tac ctxt [@{thm rewrite_terminates_with_res_IMP_Tailcall_value}]
  THEN' HTIU.SIMPS_TO_UNIF_refl_tac simp_tac ctxt

fun THEN_ALL_NEW_OFFSET offset tac1 tac2 i st =
  st |> (tac1 i THEN (fn st' =>
    st' |> Seq.INTERVAL tac2 i (i + Thm.nprems_of st' - Thm.nprems_of st - offset)));

fun subst_HOL_fun_eq_tac thms ctxt = THEN_ALL_NEW_OFFSET 1 (HTIU.subst_first_tac ctxt thms)
  (HTITG.solve_Rel_nat_tac ctxt)

(*run the HOL function to its return value or to a recursive call*)
fun run_HOL_fun_tac get_HOL_eqs ctxt =
  let fun tac {v,...} = case get_HOL_eqs ctxt (head_of v) of
      NONE => (@{log Logger.WARN} ctxt (fn _ => Pretty.block [
          Pretty.str "Could not find HOL equality for term ",
          Syntax.pretty_term ctxt v,
          Pretty.str " in conclusion."
        ] |> Pretty.string_of);
        K no_tac)
    | SOME thms => simp_res_value_tac (
          subst_HOL_fun_eq_tac thms ctxt
          THEN' delete_IH_prems
          THEN' TRY o safe_asm_full_simp_tac (ctxt delsimps thms addsimps
            @{thm Let_def} :: HTITG.get_HOL_To_IMP_finish_simps ctxt)
        ) ctxt
  in with_dest_terminates_with_res_IMP_Tailcall_prop ctxt tac end

fun finish_tac get_HOL_eqs ctxt =
  run_HOL_fun_tac get_HOL_eqs ctxt
  THEN' (finish_non_tail_tac ctxt ORELSE' finish_tail_tac ctxt)

fun start_run_finish_case_tac get_IMP_def get_imp_correct get_HOL_eqs ctxt =
  start_case_tac get_IMP_def ctxt
  THEN' run_tac get_imp_correct ctxt
  THEN_ALL_NEW SOLVED' (finish_tac get_HOL_eqs ctxt)

fun start_run_finish_tac is_induction get_fun_inducts get_IMP_def get_imp_correct get_HOL_eqs
  ctxt =
  (if is_induction then setup_induction_tac get_fun_inducts ctxt else K all_tac)
  THEN' K
    (PARALLEL_ALLGOALS (start_run_finish_case_tac get_IMP_def get_imp_correct get_HOL_eqs ctxt))

end
