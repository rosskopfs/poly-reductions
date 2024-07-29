(*  Title:  Refinements/hol_to_imp_tailcalls_tactics.ML
    Author: Kevin Kappelmann

Tactics to run IMP-Tailcall programs, track their states changes, and prove their
correspondence with HOL programs.
*)
signature HOL_TO_IMP_TAILCALLS_TACTICS =
sig
include HAS_LOGGER

(*
(*retrieve definition equality theorem from program constant*)
type IMP_def_retrieval = Proof.context -> term -> thm option
val get_IMP_def : IMP_def_retrieval

val start_tac : IMP_def_retrieval -> Proof.context -> int -> tactic
val seq_tac : Proof.context -> int -> tactic
val assign_tac : Proof.context -> int -> tactic

(*retrieve functional correctness theorem from program constant*)
type func_corrects_retrieval = Proof.context -> term -> thm list option
val get_func_corrects : func_corrects_retrieval

val call_tac : func_corrects_retrieval -> Proof.context -> int -> tactic

val if_tac : Proof.context -> int -> tactic

val run_single_tac : func_corrects_retrieval -> Proof.context -> int -> tactic

val run_tac : func_corrects_retrieval -> Proof.context -> int -> tactic

val start_run_tac : IMP_def_retrieval -> func_corrects_retrieval -> Proof.context -> int -> tactic

val finish_non_tailcall_tac : HOL_To_IMP_Tactics_Base.HOL_eqs_retrieval -> Proof.context -> int -> tactic

val tailcall_tac : Proof.context -> int -> tactic

val get_IMP_keys : HOL_To_IMP_Tactics_Base.IMP_keys_retrieval
val rewrite_insert_current_keys_eq_tac : Proof.context -> int -> tactic

val finish_tailcall_tac : HOL_To_IMP_Tactics_Base.HOL_eqs_retrieval -> Proof.context -> int -> tactic
val finish_tac : HOL_To_IMP_Tactics_Base.HOL_eqs_retrieval -> Proof.context -> int -> tactic

val start_run_finish_tac : IMP_def_retrieval  -> func_corrects_retrieval ->
  HOL_To_IMP_Tactics_Base.HOL_eqs_retrieval -> Proof.context -> int -> tactic
*)

end

structure HOL_To_IMP_Tailcalls_Tactics (* : HOL_TO_IMP_TAILCALLS_TACTICS *) =
struct

val logger = Logger.setup_new_logger HOL_To_IMP_Tactics_Base.logger "HOL_To_IMP_Tailcalls_Tactics"

structure HTITB = HOL_To_IMP_Tactics_Base
structure GU = General_Util
structure TU = Tactic_Util
structure HTIU = HOL_To_IMP_Util
structure SUT = State_Update_Tracking

structure Seq = HTIU.Seq
structure List = HTIU.List
structure Option = HTIU.Option

type IMP_def_retrieval = Proof.context -> term -> thm option
val get_IMP_def = Compile_Nat.get_compiled_const_def

(* destructors for IMP-Tailcalls *)

type terminates_with_res_IMP_Tailcall_args = {tc: term, c: term, s: term, r: term, v: term}
type terminates_with_IMP_Tailcall_args = {tc: term, c: term, s: term, s': term}

val dest_terminates_with_res_IMP_Tailcall =
  \<^Const_fn>\<open>terminates_with_res_IMP_Tailcall for tc c s r v => \<open>{tc = tc, c = c, s = s, r = r, v = v}\<close>\<close>
val dest_terminates_with_res_IMP_Tailcall_prop =
  HTIU.dest_Trueprop #> dest_terminates_with_res_IMP_Tailcall

val dest_terminates_with_IMP_Tailcall =
  \<^Const_fn>\<open>terminates_with_IMP_Tailcall for tc c s s' => \<open>{tc = tc, c = c, s = s, s' = s'}\<close>\<close>
val dest_terminates_with_IMP_Tailcall_prop =
  HTIU.dest_Trueprop #> dest_terminates_with_IMP_Tailcall

fun with_dest_tac msg dest tac =
  let fun wrap_tac concl =
    case try dest concl of
      NONE => (writeln msg; K no_tac)
    | SOME x => tac x
  in TU.SUBGOAL_STRIPPED (snd o snd) wrap_tac end

val with_dest_terminates_with_res_IMP_Tailcall_prop =
  with_dest_tac "couldn't find dest_terminates_with_res_IMP_Tailcall in conclusion"
    dest_terminates_with_res_IMP_Tailcall_prop

val with_dest_terminates_with_IMP_Tailcall_prop =
  with_dest_tac "couldn't find dest_terminates_with_IMP_Tailcall in conclusion"
    dest_terminates_with_IMP_Tailcall_prop


(* destructors for IMP-Minus *)

val dest_terminates_with_res_IMP_Minus =
  \<^Const_fn>\<open>terminates_with_res_IMP_Minus for c s r v => \<open>(c, s, r, v)\<close>\<close>

val dest_tailcall_to_IMP_Minus =
  \<^Const_fn>\<open>tailcall_to_IMP_Minus for c => c\<close>

val dest_terminates_with_res_IMP_Minus_tailcall_to_IMP_Minus =
  dest_terminates_with_res_IMP_Minus #> (fn (c, _, _, _) => c) #> dest_tailcall_to_IMP_Minus

val dest_terminates_with_res_IMP_Minus_tailcall_to_IMP_Minus_prop =
  HTIU.dest_Trueprop #> dest_terminates_with_res_IMP_Minus_tailcall_to_IMP_Minus

(* starting tactics *)

fun preprocess_tac get_IMP_def =
  let fun tac ctxt conclusion =
    case try dest_terminates_with_res_IMP_Minus_tailcall_to_IMP_Minus_prop conclusion of
      NONE =>
        (@{log Logger.WARN} ctxt (fn _ => Pretty.block [
          Pretty.str "Could not find ",
          Syntax.pretty_term ctxt @{term tailcall_to_IMP_Minus},
          Pretty.str " big step in conclusion ",
          Syntax.pretty_term ctxt conclusion
        ] |> Pretty.string_of);
        K no_tac)
      | SOME c =>
        let val solve_simple_goal_tac =
          (EqSubst.eqsubst_tac ctxt [0] (get_IMP_def ctxt c |> the_list)
          THEN' Simplifier.simp_tac ctxt)
          |> SOLVED'
        in
          resolve_tac ctxt [@{thm terminates_with_res_IMP_Minus_if_terminates_with_res_IMP_TailcallI}]
          (* solve the invariant: invar f_IMP_tailcall *)
          THEN' solve_simple_goal_tac
          (* solve the assumption: ''f.ret'' in vars f_IMP_tailcall *)
          THEN' solve_simple_goal_tac
        end
  in TU.SUBGOAL_STRIPPED (snd o snd) o tac end

fun flip_eq_thm ctxt thm = Thm.proof_attributes [Calculation.symmetric] thm ctxt |> fst

val rewrite_eq_state_retrieval_sym_tac =
  let
    fun rewrite_focused_tac {prems, context = ctxt, ...} =
      let val prems_flipped = map (flip_eq_thm ctxt) prems
      in
        REPEAT_ALL_NEW (HTIU.subst_first_tac ctxt prems_flipped)
        THEN' TU.insert_tac prems_flipped ctxt
      end
    fun rewrite_tac ctxt prems {s, ...}  =
      let
        val is_eq_state_retrieval_prem =
          GU.try_bool
            (HTIU.dest_Trueprop #>
            \<^Const_fn>\<open>HOL.eq _ for _ s_app => \<open>SUT.is_state_state_retrieval s s_app\<close>\<close>)
        val eq_state_retrieval_prems = GU.find_indices is_eq_state_retrieval_prem prems
      in
        TU.focus_delete_prems_tac (HTIU.successors eq_state_retrieval_prems)
          rewrite_focused_tac ctxt
      end
  in
    TU.FOCUS_PARAMS_CTXT' (
      TU.SUBGOAL_STRIPPED (fst o snd) o (
        with_dest_terminates_with_res_IMP_Tailcall_prop oo rewrite_tac))
  end

fun setup_induction_tac get_inducts =
  let fun focused_tac ctxt {s, v, ...} =
    let
      (* v is of the form f (s ''...'') (s ''...'') ..., where f is the HOL function we are after *)
      val head = head_of v
      val instantiations =
        head |> dest_Const |> fst
        |> Compile_Nat.get_compiled_const (Context.Proof ctxt) |> #arg_regs
        |> map (HOL_To_IMP_Util.mk_state_register_retrieval s)
        |> map (fn t => SOME (NONE, (t, false)))
      val arbitrary = [dest_Free s]
      val inducts = get_inducts ctxt head
    in
      Induction.induction_tac ctxt true [instantiations] [arbitrary] [] inducts []
      (* needed for inductions of functions defined on pattern matching; they create equalities of the
         form "t = s ''<register>''", which have to be rewritten in the goal's conclusion" *)
      THEN_ALL_NEW (TU.TRY' (rewrite_eq_state_retrieval_sym_tac ctxt))
    end
  in TU.FOCUS_PARAMS_CTXT' (with_dest_terminates_with_res_IMP_Tailcall_prop o focused_tac) end

fun start_case_tac get_IMP_def =
  let fun focused_tac ctxt {c, ...} =
    EqSubst.eqsubst_tac ctxt [2] (get_IMP_def ctxt c |> the_list)
    THEN' resolve_tac ctxt [@{thm terminates_with_res_IMP_Tailcall_start}]
  in TU.FOCUS_PARAMS_CTXT' (with_dest_terminates_with_res_IMP_Tailcall_prop o focused_tac) end


(* tactics for tAssign, tSeq, and tIf that run one step of the tailcall program *)

val terminates_with_res_tAssign_tac = HTITB.assign_tac [@{thm terminates_with_res_tAssignI}]
val terminates_with_res_tSeq_tac = HTITB.seq_tac [@{thm terminates_with_res_tSeqI}]
val terminates_with_res_tIf_tac = HTITB.if_tac [@{thm terminates_with_res_tIf_processedI}]


(* tactics for tAssign and tCall that handle terminates_with (instead of terminates_with_res) *)

val terminates_with_tAssign_tac = HTITB.assign_tac [@{thm terminates_with_tAssignI}]

fun terminates_with_tCall_tac get_func_corrects =
  let fun tac ctxt {c, ...} =
    case c of
      Const (@{const_name tCall}, _) $ com $ _ =>
        (case get_func_corrects ctxt com of
            NONE => (writeln "no correctness found"; K no_tac (* TODO: error message *))
          | SOME cs => HTITB.call_tac [@{thm terminates_with_tCallI}] ctxt cs)
    | _ => K no_tac
  in with_dest_terminates_with_IMP_Tailcall_prop o tac end

type func_corrects_retrieval = Proof.context -> term -> thm list option
(* given a constant term like eq_IMP, returns a list of potentially suitable IMP- correctness theorems *)
fun get_func_corrects ctxt t =
  let
    open Find_Theorems
    val thms = find_theorems ctxt NONE NONE true [
      (* search for the equality theorem *)
      (true, Pattern (@{term terminates_with_res_IMP_Minus} $ t (* TODO: wildcard for remaining args? *))),
      (* ignore conditional rules *)
      (false, Pattern @{term "(\<Longrightarrow>)"})
    ] |> snd |> map snd
  in if null thms then NONE else SOME thms end

fun run_step_tac get_func_corrects ctxt =
  HTITB.run_step_tac
    (terminates_with_res_tSeq_tac ctxt)
    (terminates_with_tAssign_tac ctxt)
    (terminates_with_tCall_tac get_func_corrects ctxt)
    (terminates_with_res_tIf_tac ctxt)

(* run a tailcall program to completion,
   ends with terminates_with_res _ c _ _ _, where c is either an assignment, or tTAIL *)
fun run_tac get_func_corrects = HTITB.run_tac o run_step_tac get_func_corrects


(* finishing tactics *)

val finish_tail_tac =
  let
    open Seq.M
    open HTIU.Let

    (* get a list of theorems of the form t_i = s ''reg_i'',
       one for each argument in the function application term v *)
    fun get_reg_eq_thms ctxt arg_reg_eq_tac s v =
      (* v is of the form f t1 t2 ..., where f is the relevant HOL function;
         extract the head f, and the terms t1, t2, ... *)
      Term.strip_comb v
      LET (fn (head, arg_terms) =>
        (* fetch the compiled constant *)
        Basics.try (dest_Const #> fst #> Compile_Nat.get_compiled_const (Context.Proof ctxt)) head
        |> HTIU.seq_of_opt (fn () => writeln "could not load compiled constant" (* todo msg *))
      BIND (fn {arg_regs, ...} =>
        (* construct equalities of the form t_i = s ''reg_i'' *)
        map2
          (fn t => fn reg =>
            HTIU.mk_eq (t, HTIU.mk_state_register_retrieval s reg)
            |> HTIU.mk_Trueprop |> Thm.cterm_of ctxt)
          arg_terms arg_regs
      LET (fn arg_reg_eqs =>
        (* prove the equalities *)
        arg_reg_eqs |> List.map (TU.HEADGOAL (TU.apply_tac (SOLVED' arg_reg_eq_tac))) |> List.T_Seq.sequence
        (* this might not be an actual warning: if we simplify the HOL call incorrectly, a backtrack would be ok *)
        |> HTIU.seq_peek_empty (fn () => writeln "could not prove one or more register equalities")
        (* TODO: show the user which could not be proven? this would be pretty helpful if cooking fails *)
      )))

    (* tactic for proving the equalities: add existing premises, then simp *)
    fun arg_reg_eq_tac ctxt prems =
      Tactic.cut_facts_tac prems
      THEN'
      (* TODO: narrow down the simpset here... or come up with a better tactic *)
      Simplifier.asm_simp_tac (
        Simplifier.clear_simpset ctxt
        addsimps @{thms STATE_eq interp_update_state_eq interp_state_State_eq})
      THEN' Simplifier.asm_simp_tac ctxt

    (* rewrite each argument t_i to s ''reg_i'' *)
    fun rewrite_conclusion_arguments_tac ctxt arg_reg_eq_thms =
      let
        (* each argument is first drawn out into a separate subgoal t_i = ?v s
           to prevent substitution from occurring inside s *)
        fun rewrite_args_tac [] = HTIU.refl_tac ctxt
          | rewrite_args_tac (thm :: thms) =
              HTIU.uresolve_tac ctxt [@{thm rewrite_comb}]
              THEN' rewrite_args_tac thms
              THEN' HTIU.subst_first_tac ctxt [thm] THEN' HTIU.refl_tac ctxt
      in
        resolve_tac ctxt [@{thm rewrite_terminates_with_res_IMP_Tailcall_value}]
        THEN' rewrite_args_tac (rev arg_reg_eq_thms)
      end

    fun solve_with_ih_tac ctxt prems s arg_reg_eq_thms =
      let
        val is_ih = Thm.concl_of #> can dest_terminates_with_res_IMP_Tailcall_prop

        val s_ct = Thm.cterm_of ctxt s
        val s_typ = Term.fastype_of s

        (* induction hypotheses can have multiple free variables, find them all *)
        val insts =
          Thm.prop_of
          #> fold_aterms (fn Var v => insert (op =) v | _ => I) #> build_rev
          #> List.filter (fn (_, typ) => typ = s_typ)
          #> List.map (fn (name, _) => (name, s_ct))

        val instantiate_apply_ih_tac =
          Seq.of_list prems
          |> Seq.filter is_ih
          BIND (fn ih =>
            insts ih |> Seq.of_list
          BIND (fn inst =>
            try (Drule.infer_instantiate ctxt [inst]) ih |> Option.to_seq
          BIND (fn ih_inst =>
            resolve_tac ctxt [ih_inst] |> Seq.A.pure
          )))
          |> flat2

        val solve_ih_prem_tac =
          Tactic.cut_facts_tac prems
          THEN' TU.TRY' (HTIU.subst_first_tac ctxt (List.map (flip_eq_thm ctxt) arg_reg_eq_thms))
          THEN' Simplifier.asm_simp_tac ctxt (* TODO: narrow simp set *)
      in
        instantiate_apply_ih_tac THEN_ALL_NEW SOLVED' solve_ih_prem_tac
      end

    fun prems_tac {context = ctxt, prems, ...} {s, v, ...} =
      get_reg_eq_thms ctxt (arg_reg_eq_tac ctxt prems) s v
      BIND (fn arg_reg_eq_thms =>
        rewrite_conclusion_arguments_tac ctxt arg_reg_eq_thms
        THEN' solve_with_ih_tac ctxt prems s arg_reg_eq_thms
        |> pure)
      |> flat2

    fun focused_tac ctxt =
      resolve_tac ctxt [@{thm terminates_with_res_tTailI}]
      THEN' TU.FOCUS_PREMS' (with_dest_terminates_with_res_IMP_Tailcall_prop o prems_tac) ctxt
  in
    TU.FOCUS_PARAMS_CTXT' focused_tac
  end

fun finish_non_tail_tac ctxt =
  terminates_with_res_tAssign_tac ctxt
  THEN' HTITB.STATE_interp_retrieve_key_eq_tac (asm_simp_tac (ctxt addsimps (@{thms Let_def}))) ctxt


(* common tail/non-tail finish tactics *)

(* run the HOL function to its return value or to a recursive call *)
fun run_hol_fun_tac get_HOL_eqs =
  let fun tac ctxt {v, ...} =
    case get_HOL_eqs ctxt (head_of v) of
      NONE => (writeln "Could not find HOL equality for HOL term in conclusion"; (* TODO *) K no_tac)
    | SOME thms =>
        HTIU.subst_first_tac ctxt thms
        (* TODO: the simplification step is fragile if there is any
          other theorem about the HOL function in the simpset *)
        (* TODO: target the relevant assumptions only (?) *)
        (* TODO: anything beyond Let_def? Should simplification be consolidated somewhere? *)
        THEN' TU.TRY' (Simplifier.asm_simp_tac (ctxt addsimps (@{thms Let_def})))
  in with_dest_terminates_with_res_IMP_Tailcall_prop o tac end

fun finish_tac get_HOL_eqs =
  let fun tac ctxt =
    run_hol_fun_tac get_HOL_eqs ctxt
    THEN' (finish_tail_tac ctxt ORELSE' finish_non_tail_tac ctxt)
  in TU.FOCUS_PARAMS_CTXT' tac end

fun correct_tac is_tailcall get_HOL_inducts get_IMP_def get_func_corrects get_HOL_eqs =
  let fun tac ctxt =
    preprocess_tac get_IMP_def ctxt
    THEN' (if is_tailcall then setup_induction_tac get_HOL_inducts ctxt else K all_tac)
    THEN_ALL_NEW (
      start_case_tac get_IMP_def ctxt
      THEN' run_tac get_func_corrects ctxt
      THEN_ALL_NEW (
        finish_tac get_HOL_eqs ctxt
        ORELSE' SOLVED' (Simplifier.asm_simp_tac ctxt)
        ORELSE' K all_tac))
  in TU.FOCUS_PARAMS_CTXT' tac end

end
