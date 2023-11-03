theory HOL_To_IMP_Minus_Goal_Commands
  imports Compile_Nat
  keywords "HOL_To_IMP_Minus_func_correct" :: thy_goal_defn
begin

ML \<open>
structure HOL_To_IMP_Minus_Func_Correct_Thms = Generic_Data
(
  type T = thm Termtab.table;
  val empty = Termtab.empty
  val merge = Termtab.join (K fst)
)

structure HOL_To_IMP_Minus_Func_Correct_Thms = struct
open HOL_To_IMP_Minus_Func_Correct_Thms

fun func_correct_attr c =
  Thm.declaration_attribute (fn thm => map (Termtab.update_new (c, thm)))

val get_theorem = Termtab.lookup o get o Context.Proof
end
\<close>

attribute_setup IMP_Minus_func_correct = \<open>
  Scan.lift Parse.const :|-- (fn cs => fn (context, tks) =>
    let
      val ctxt = Context.proof_of context
      val c = Proof_Context.read_const {proper = false, strict = false} ctxt cs
    in
      (HOL_To_IMP_Minus_Func_Correct_Thms.func_correct_attr c, (context, tks))
    end)
\<close>

ML \<open>
local
  val parser =
    Scan.optional (Parse_Spec.opt_thm_name ":") Binding.empty_atts --
    Parse.const
in
  val _ =
    Outer_Syntax.local_theory_to_proof'
      \<^command_keyword>\<open>HOL_To_IMP_Minus_func_correct\<close>
      "setup goal to refine HOL tail-recursive functions over nats to IMP-"
      (parser >> (fn (binding, const) => fn b => fn lthy =>
        let
          val const_term = Proof_Context.read_const {proper = false, strict = false} lthy const
          val compiled_const =
            Term.dest_Const const_term |> fst
            |> Compile_Nat.get_compiled_const (Context.Proof lthy)
          val IMP_program = #compiled compiled_const
          val [s, s', t] = Variable.variant_fixes ["s", "s'", "t"] lthy |> fst
          val (s, s') = @{apply 2} (fn v => Free (v, \<^typ>\<open>AExp.state\<close>)) (s, s')
          val t = Free (t, \<^typ>\<open>nat\<close>)
          val big_step_t_asm =
            \<^Const>\<open>Pair \<^typ>\<open>com\<close> \<^typ>\<open>AExp.state\<close> for \<open>IMP_program\<close> s\<close>
            |> (fn cs => \<^Const>\<open>big_step_t for cs t s'\<close>)
            |> HOLogic.mk_Trueprop
          val ret_reg = s' $ HOLogic.mk_string (#ret_reg compiled_const)
          fun arg_reg reg = s $ HOLogic.mk_string reg
          val goal =
            \<^Const>\<open>HOL.eq \<^typ>\<open>nat\<close> for
              ret_reg
              \<open>Term.list_comb (const_term, map arg_reg (#arg_regs compiled_const))\<close>
            \<close>
            |> HOLogic.mk_Trueprop
            |> (fn g => Logic.mk_implies (big_step_t_asm, g))
          val goal_stmt = Element.Shows [(Binding.empty_atts, [(goal, [])])]

          val pos = Position.thread_data ()
          val func_correct_attr =
            Attrib.internal pos (fn phi =>
              HOL_To_IMP_Minus_Func_Correct_Thms.func_correct_attr (Morphism.term phi IMP_program))
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
\<close>

end