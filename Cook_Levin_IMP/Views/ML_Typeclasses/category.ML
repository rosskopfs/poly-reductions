(*  Title: category.ML
    Author: Kevin Kappelmann

Basic typeclasses related to category theory, inspired by the Haskell base package.
*)
signature CATEGORY_BASE =
sig

type ('a, 'b) cat
val id : ('a, 'a) cat
val comp : ('b, 'c) cat -> ('a, 'b) cat -> ('a, 'c) cat

end

signature ARROW_BASE =
sig

include CATEGORY_BASE
val arr : ('a -> 'b) -> ('a, 'b) cat
val *** : ('a, 'b) cat -> ('c, 'd) cat -> (('a * 'c), ('b * 'd)) cat

end

signature ARROW =
sig

include ARROW_BASE

val first : ('a, 'b) cat -> (('a * 'c), ('b * 'c)) cat
val second : ('a, 'b) cat -> (('c * 'a), ('c * 'b)) cat

end

functor Arrow(A : ARROW_BASE) : ARROW =
struct

open A
fun first f = *** f id
fun second f = *** id f

end

signature KLEISLI =
sig

structure M : MONAD_BASE

type ('a, 'b) kleisli
val interp : ('a, 'b) kleisli -> 'a -> 'b M.t

(*Kleisli category*)
include ARROW_BASE
sharing type cat = kleisli

end

functor Kleisli(M : MONAD_BASE) : KLEISLI =
struct

structure M = M

datatype ('a, 'b) kleisli = Kleisli of 'a -> 'b M.t
fun interp (Kleisli f) = f

(*ARROW_BASE instance*)
type ('a, 'b) cat = ('a, 'b) kleisli
val id = Kleisli M.pure
fun comp k1 k2 = Kleisli (fn x => M.bind (interp k2 x) (interp k1))
fun arr f = Kleisli (M.pure o f)
fun *** k1 k2 = Kleisli (fn (x, y) => M.bind (interp k1 x)
  (fn x' => M.bind (interp k2 y) 
  (fn y' => M.pure (x', y'))))

end
