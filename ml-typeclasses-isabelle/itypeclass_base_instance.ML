(*  Title:  itypeclass_base_instance.ML
    Author: Kevin Kappelmann

Instances of basic indexed typeclasses.
*)
functor IMonad_Exception_IMonad_Or(M : IMONAD_OR_BASE)
  : IMONAD_EXCEPTION_BASE where type 'p1 exn = unit =
struct
open M
type 'p1 exn = unit

val throw = zero
val catch = or_lazy
end
