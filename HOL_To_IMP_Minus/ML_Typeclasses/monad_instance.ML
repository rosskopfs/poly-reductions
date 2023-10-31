(*  Title: monad_instance.ML
    Author: Kevin Kappelmann

Instances of monads.
*)
structure Id_Monad_Base : MONAD_BASE =
struct

type 'a t = 'a
fun map f x = f x
fun pure x = x
fun <*> f x = f x
fun bind x f = f x

end
                            
structure Seq_Monad_Base : MONAD_BASE =
struct

open Seq
type 'a t = 'a seq
val pure = single
fun <*> sqf sqx = Seq.maps (fn f => map f sqx) sqf
fun bind sq f = maps f sq

end