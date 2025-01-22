(*  Title:  Automation/hol_nat_to_imp_minus_goal_command.ML
    Author: Kevin Kappelmann

Setup goal for HOL to IMP- refinement.
*)
signature HOL_NAT_TO_IMP_MINUS_GOAL_COMMAND =
sig
val get_imp_minus_correct : Proof.context -> Termtab.key -> thm option

val update_imp_minus_correct : thm -> Context.generic -> Context.generic
val update_imp_minus_correct_attr : attribute

val delete_imp_minus_correct : thm -> Context.generic -> Context.generic
val delete_imp_minus_correct_attr : attribute

val setup_imp_minus_correct_attr : attribute context_parser
end

structure HOL_Nat_To_IMP_Minus_Goal_Command : HOL_NAT_TO_IMP_MINUS_GOAL_COMMAND =
struct

structure HTIU = HOL_Nat_To_IMP_Util
structure HTHNU = HOL_To_HOL_Nat_Util

fun mk_terminates_with_res_IMP_Minus c s r v = \<^Const>\<open>terminates_with_res_IMP_Minus for c s r v\<close>
val dest_terminates_with_res_IMP_Minus =
  \<^Const_fn>\<open>terminates_with_res_IMP_Minus for c s r v => \<open>(c, s, r, v)\<close>\<close>

val compiled_const_from_thm = Thm.concl_of #> HTIU.dest_Trueprop #> dest_terminates_with_res_IMP_Minus
  #> (fn (c, _, _, _) => c)

structure HOL_To_IMP_Minus_IMP_Minus_Correct_Thms = Generic_Data
(
  type T = thm Termtab.table
  val empty = Termtab.empty
  val merge = Termtab.join (K fst)
)

val get_imp_minus_correct =
  Termtab.lookup o HOL_To_IMP_Minus_IMP_Minus_Correct_Thms.get o Context.Proof

fun update_imp_minus_correct thm =
  compiled_const_from_thm thm
  |> rpair thm
  |> Termtab.update_new
  |> HOL_To_IMP_Minus_IMP_Minus_Correct_Thms.map
val update_imp_minus_correct_attr = Thm.declaration_attribute update_imp_minus_correct

fun delete_imp_minus_correct thm = compiled_const_from_thm thm
  |> Termtab.delete
  |> HOL_To_IMP_Minus_IMP_Minus_Correct_Thms.map
val delete_imp_minus_correct_attr = Thm.declaration_attribute delete_imp_minus_correct

val imp_minus_correct_binding = \<^binding>\<open>IMP_Minus_correct\<close>

val setup_imp_minus_correct_attr = Attrib.add_del
  update_imp_minus_correct_attr delete_imp_minus_correct_attr

val _ = Theory.setup (
  Attrib.setup imp_minus_correct_binding setup_imp_minus_correct_attr
    "add/del IMP- functional correctness theorem")

local
  val parser =
    Scan.optional (Parse_Spec.opt_thm_name ":") Binding.empty_atts --
    Parse.position Parse.const
in
  val _ =
    Outer_Syntax.local_theory_to_proof'
      \<^command_keyword>\<open>HOL_To_IMP_Minus_correct\<close>
      "setup goal to refine HOL tail-recursive functions over nats to IMP-"
      (parser >> (fn (binding_attrs, (const, pos)) => fn b => fn lthy =>
        let
          val stateT = \<^typ>\<open>AExp.state\<close>
          val const_term = HTHNU.read_const lthy const
          val compiled_const = const_term
            |> Compile_HOL_Nat_To_IMP.get_compiled_const lthy

          val (s, lthy) = yield_singleton Variable.variant_fixes "s" lthy |>> (rpair stateT #> Free)
          val base_args = #arg_regs compiled_const |> map (HTIU.mk_state_register_retrieval s)

          val opt_eq_unfolded_thm = const_term
            |> HOL_Fun_To_HOL_Nat_Fun.get_compiled_eq_unfolded lthy
            |> Option.map (
                Thm.instantiate' [] (List.concat
                  (map (fn x => [x |> Thm.cterm_of lthy |> SOME, NONE]) base_args))
                #> Variable.import_vars lthy)

          val (prems, args) = case opt_eq_unfolded_thm of
              NONE => ([], base_args)
            | SOME eq_unfolded_thm =>
                let val TYPEs = Thm.concl_of eq_unfolded_thm |> HTHNU.dest_eq_equals_prop |> fst
                  |> strip_comb |> snd |> filter HTHNU.is_TYPE
                in (Thm.prems_of eq_unfolded_thm, TYPEs @ base_args) end
          val HOLt = Term.list_comb (Transport.map_dummyT const_term, args)
            |> Syntax.check_term lthy

          val IMP_program = #compiled compiled_const
          val ret_reg = HTIU.mk_register (#ret_reg compiled_const)
          (*TODO: move terminates_with_res stuff to utility module*)
          val concl = mk_terminates_with_res_IMP_Minus IMP_program s ret_reg HOLt
            |> HTIU.mk_Trueprop
          val goal = Logic.list_implies (prems, concl)
          val goal_stmt = Element.Shows [(Binding.empty_atts, [(goal, [])])]

          val imp_minus_correct_attr = Attrib.internal pos (K update_imp_minus_correct_attr)
          val binding_attrs = binding_attrs
            |>> (fn binding => if Binding.is_empty binding
              then Transport_Util.add_suffix (HTHNU.const_binding const_term)
                imp_minus_correct_binding |> Binding.set_pos pos
              else binding)
            ||> cons imp_minus_correct_attr
        in
          Specification.theorem false Thm.theoremK NONE (K I) binding_attrs [] [] goal_stmt b lthy
        end
      ))
 end

 end