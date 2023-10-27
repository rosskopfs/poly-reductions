theory Refine_Nat
  imports Compile_Nat
  keywords "refine_nat_goal" :: thy_decl
begin

ML \<open>
structure Refine_Nat_Thms = Generic_Data
(
  type T = thm Termtab.table;
  val empty = Termtab.empty
  val merge = Termtab.join (K fst)
)

structure Refine_Nat_Thms = struct
open Refine_Nat_Thms

fun refine_nat_attr c =
  Thm.declaration_attribute (fn thm => Refine_Nat_Thms.map (Termtab.update_new (c, thm)))

end
\<close>

attribute_setup refine_nat = \<open>
  Scan.lift Parse.const :|-- (fn cs => fn (context, tks) =>
    let
      val ctxt = Context.proof_of context
      val c = Proof_Context.read_const {proper = true, strict = true} ctxt cs
    in
      (Refine_Nat_Thms.refine_nat_attr c, (context, tks))
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
      \<^command_keyword>\<open>refine_nat_goal\<close>
      "setup goal to refine tail-recursive functions over nats to IMP- with tail-calls"
      (parser >> (fn (binding, const) => fn b => fn lthy =>
        let
          val const_term = Proof_Context.read_const {proper = true, strict = true} lthy const
          val compiled_const =
            Term.dest_Const const_term |> fst
            |> Compile_Nat.get_compiled_const (Context.Proof lthy)
          val [s, s', t] = Variable.variant_fixes ["s", "s'", "t"] lthy |> fst
          val (s, s') = @{apply 2} (fn v => Free (v, \<^typ>\<open>AExp.state\<close>)) (s, s')
          val t = Free (t, \<^typ>\<open>nat\<close>)
          val big_step_t_asm =
            \<^Const>\<open>Pair \<^typ>\<open>com\<close> \<^typ>\<open>AExp.state\<close> for \<open>#compiled compiled_const\<close> s\<close>
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
          val attr = Refine_Nat_Thms.refine_nat_attr
          val refine_nat_attr =
            Attrib.internal pos (fn phi => attr (Morphism.term phi const_term))
        in
          lthy
          |> Specification.theorem false Thm.theoremK NONE (K I)
              (binding ||> (fn atts => refine_nat_attr :: atts)) [] [] goal_stmt b
        end
      ))
end
\<close>

end