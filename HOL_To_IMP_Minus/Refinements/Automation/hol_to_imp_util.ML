signature HOL_TO_IMP_UTIL =
sig

val mk_register : string -> term
val mk_state_register_retrieval : term -> string -> term

end

structure HOL_To_IMP_Util : HOL_TO_IMP_UTIL =
struct

structure SIT = State_IMP_Tailcalls

val mk_register = HOLogic.mk_string
fun mk_state_register_retrieval state = SIT.mk_state_retrieval state o mk_register

end