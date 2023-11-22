(*  Title: Refinements/hol_to_imp_util.ML
    Author: Kevin Kappelmann

More utilities when refining HOL to IMP programs.
*)
signature HOL_TO_IMP_UTIL =
sig
include HOL_TO_IMP_UTIL

val dest_IMP_Minus_big_step : term -> (term * term) * term * term
val mk_IMP_Minus_big_step : typ -> term -> term -> term -> term -> term

val mk_register : string -> term
val mk_state_register_retrieval : term -> string -> term
end

structure HOL_To_IMP_Util : HOL_TO_IMP_UTIL =
struct

open HOL_To_IMP_Util
structure SUT = State_Update_Tracking

val dest_IMP_Minus_big_step =
  \<^Const_fn>\<open>big_step_t for \<^Const>\<open>Pair _ _ for c s\<close> t s' => \<open>((c, s), t, s')\<close>\<close>

fun mk_IMP_Minus_big_step state IMP_program s t s'=
  \<^Const>\<open>Pair \<^typ>\<open>com\<close> state for \<open>IMP_program\<close> s\<close>
  |> (fn cs => \<^Const>\<open>big_step_t for cs t s'\<close>)

val mk_register = HOLogic.mk_string
fun mk_state_register_retrieval state = SUT.mk_state_retrieval state o mk_register

end