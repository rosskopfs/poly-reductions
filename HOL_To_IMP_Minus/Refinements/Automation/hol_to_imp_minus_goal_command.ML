(*  Title:  Refinements/hol_to_imp_minus_goal_command.ML
    Author: Kevin Kappelmann

Setup goal for HOL to IMP- refinement.
*)

signature HOL_TO_IMP_MINUS_GOAL_COMMAND =
sig
val get_func_corrects : Proof.context -> Termtab.key -> thm option

val update_func_correct : thm -> Context.generic -> Context.generic
val update_func_correct_attr : attribute

val delete_func_correct : thm -> Context.generic -> Context.generic
val delete_func_correct_attr : attribute

val setup_func_correct_attr : attribute context_parser
end

structure HOL_To_IMP_Minus_Goal_Command : HOL_TO_IMP_MINUS_GOAL_COMMAND =
struct

structure HTIU = HOL_To_IMP_Util

val compiled_const_from_thm = Thm.prems_of
  #> map_filter (try (HTIU.dest_Trueprop #> HTIU.dest_IMP_Minus_big_step))
  #> hd #> (fn ((c, _), _, _) => c)

structure HOL_To_IMP_Minus_Func_Correct_Thms = Generic_Data
(
  type T = thm Termtab.table
  val empty = Termtab.empty
  val merge = Termtab.join (K fst)
)

val get_func_corrects =
  Termtab.lookup o HOL_To_IMP_Minus_Func_Correct_Thms.get o Context.Proof

fun update_func_correct thm =
  compiled_const_from_thm thm
  |> rpair thm
  |> Termtab.update_new
  |> HOL_To_IMP_Minus_Func_Correct_Thms.map
val update_func_correct_attr = Thm.declaration_attribute update_func_correct

fun delete_func_correct thm = compiled_const_from_thm thm
  |> Termtab.delete
  |> HOL_To_IMP_Minus_Func_Correct_Thms.map
val delete_func_correct_attr = Thm.declaration_attribute delete_func_correct

val func_correct_binding = \<^binding>\<open>IMP_Minus_func_correct\<close>

val setup_func_correct_attr = Attrib.add_del
  update_func_correct_attr delete_func_correct_attr

val _ = Theory.setup (
  Attrib.setup func_correct_binding setup_func_correct_attr
    "add/del IMP- functional correctness theorem")

local
  val parser =
    Scan.optional (Parse_Spec.opt_thm_name ":") Binding.empty_atts --
    Parse.position Parse.const
in
  val _ =
    Outer_Syntax.local_theory_to_proof'
      \<^command_keyword>\<open>HOL_To_IMP_Minus_func_correct\<close>
      "setup goal to refine HOL tail-recursive functions over nats to IMP-"
      (parser >> (fn (binding, (const, pos)) => fn b => fn lthy =>
        let
          val stateT = \<^typ>\<open>AExp.state\<close>
          val const_term = Proof_Context.read_const {proper = false, strict = false} lthy const
          val compiled_const =
            Term.dest_Const const_term |> fst
            |> Compile_Nat.get_compiled_const (Context.Proof lthy)
          val IMP_program = #compiled compiled_const
          val [s, s', t] = Variable.variant_fixes ["s", "s'", "t"] lthy |> fst
          val (s, s') = @{apply 2} (fn v => Free (v, stateT)) (s, s')
          val t = Free (t, \<^typ>\<open>nat\<close>)
          val big_step_prem = HTIU.mk_IMP_Minus_big_step stateT IMP_program s t s'
            |> HTIU.mk_Trueprop
          val ret_reg = s' $ HTIU.mk_register (#ret_reg compiled_const)
          fun arg_reg reg = s $ HTIU.mk_register reg
          val goal =
            \<^Const>\<open>HOL.eq \<^typ>\<open>nat\<close> for
              ret_reg
              \<open>Term.list_comb (const_term, map arg_reg (#arg_regs compiled_const))\<close>
            \<close>
            |> HTIU.mk_Trueprop
            |> (fn g => Logic.mk_implies (big_step_prem, g))
          val goal_stmt = Element.Shows [(Binding.empty_atts, [(goal, [])])]

          val func_correct_attr =
            Attrib.internal pos (K update_func_correct_attr)
          val binding = binding |> Binding.is_empty (fst binding) ?
            apfst (fn _ => [Term.term_name const_term, "IMP_Minus_func_correct"]
              |> map Binding.name
              |> Binding.conglomerate
              |> Binding.set_pos pos)
        in
          lthy
          |> Specification.theorem false Thm.theoremK NONE (K I)
              (binding ||> (fn atts => func_correct_attr :: atts)) [] [] goal_stmt b
        end
      ))
end


end
