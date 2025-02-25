(*  Title:  category_instance.ML
    Author: Kevin Kappelmann

Instances of categories.
*)
(*standard function space*)
structure SArrow_Apply : ARROW_APPLY_BASE =
struct

type ('p1, 'a, 'b) cat = 'a -> 'b
fun id _ = I
fun comp f g x = f (g x)
val arr = I
fun (f *** g) (x, y) = (f x, g y)
fun app (f, x) = f x

end

structure SArrow_Arrow_Apply : ARROW_ARROW_APPLY =
struct
  structure A = Arrow(SArrow_Apply)
  structure AA = Arrow_Apply(SArrow_Apply)
end

(*Kleisli category*)
signature KLEISLI =
sig
  structure M : MONAD_BASE
  type ('p1, 'a, 'b) kleisli = 'a -> ('p1, 'b) M.t
end

functor Kleisli(M : MONAD_BASE) : KLEISLI =
struct
structure M = M
type ('p1, 'a, 'b) kleisli = 'a -> ('p1, 'b) M.t
end

signature KLEISLI_ARROW_BASE =
sig
  structure K : KLEISLI
  include ARROW_BASE
  where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) K.kleisli
end

signature KLEISLI_ARROW =
sig
  structure K : KLEISLI
  include ARROW
  where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) K.kleisli
end

signature KLEISLI_ARROW_APPLY_BASE =
sig
  structure K : KLEISLI
  include ARROW_APPLY_BASE
  where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) K.kleisli
end

functor Kleisli_Arrow_Apply_Base(M : MONAD_BASE) : KLEISLI_ARROW_APPLY_BASE =
struct

open M
structure K = Kleisli(M)
open K

type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) kleisli
fun id _ = pure
local structure M = Monad(M) open M
in
fun comp k1 k2 x = k2 x >>= k1
fun arr f = pure o f
fun k1 *** k2 = (fn (x, y) => k1 x
  >>= (fn x' => k2 y
  >>= (fn y' => pure (x', y'))))
fun app (f, x) = f x
end

end

functor Kleisli_Arrow(M : MONAD_BASE) : KLEISLI_ARROW =
struct

structure K = Kleisli_Arrow_Apply_Base(M)
open K

fun first f (x, y) = M.bind (f x) (rpair y #> M.pure)
fun second f (x, y) = M.bind (f y) (pair x #> M.pure)
fun (f &&& g) x = M.bind (f x) (fn y1 => M.bind (g x) (fn y2 => M.pure (y1, y2)))
fun K x _ = M.pure x
fun curry f x y = f (x, y)

end

signature KLEISLI_ARROW_APPLY =
sig
  structure K : KLEISLI
  include ARROW_APPLY
  where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) K.kleisli
end

functor Kleisli_Arrow_Apply(M : MONAD_BASE) : KLEISLI_ARROW_APPLY =
struct

structure K = Kleisli_Arrow_Apply_Base(M)
open K
fun app' x f = f x
fun uncurry f (x, y) = f x y

end

signature KLEISLI_ARROW_ARROW_APPLY =
sig
  structure K : KLEISLI
  include ARROW_ARROW_APPLY
  where type ('p1, 'a, 'b) A.cat = ('p1, 'a, 'b) K.kleisli
end

functor Kleisli_Arrow_Arrow_Apply(M : MONAD_BASE) : KLEISLI_ARROW_ARROW_APPLY =
struct
  structure A = Kleisli_Arrow(M)
  structure K = A.K
  structure AA = Kleisli_Arrow_Apply(M)
end

signature KLEISLI_ARROW_ZERO_BASE =
sig
  structure K : KLEISLI
  include ARROW_ZERO_BASE
  where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) K.kleisli
end

functor Kleisli_Arrow_Zero(MZ : MONAD_ZERO_BASE) : KLEISLI_ARROW_ZERO_BASE =
struct
structure AA = Kleisli_Arrow_Apply_Base(MZ)
open AA
fun zero _ _ = MZ.zero ()
end

signature KLEISLI_ARROW_PLUS_BASE =
sig
  structure K : KLEISLI
  include ARROW_PLUS_BASE
  where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) K.kleisli
end

functor Kleisli_Arrow_Plus_Base(MP : MONAD_PLUS_BASE) : KLEISLI_ARROW_PLUS_BASE =
struct
structure AZ = Kleisli_Arrow_Zero(MP)
open AZ
fun plus f g x = MP.plus_lazy (f x) (fn _ => g x)
end

signature KLEISLI_ARROW_OR_BASE =
sig
  structure K : KLEISLI
  include ARROW_OR_BASE
  where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) K.kleisli
end

functor Kleisli_Arrow_Or_Base(MO : MONAD_OR_BASE) : KLEISLI_ARROW_OR_BASE =
struct
structure AZ = Kleisli_Arrow_Zero(MO)
open AZ
fun or f g x = MO.or_lazy (f x) (fn _ => g x)
end

signature KLEISLI_ARROW_EXCEPTION_BASE =
sig
  structure K : KLEISLI
  include ARROW_EXCEPTION_BASE
  where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) K.kleisli
end

functor Kleisli_Arrow_Exception_Base(ME : MONAD_EXCEPTION_BASE) : KLEISLI_ARROW_EXCEPTION_BASE =
struct
structure AA = Kleisli_Arrow_Apply_Base(ME)
open AA
type 'p1 exn = 'p1 ME.exn
val throw = ME.throw
fun catch f g x = ME.catch (f x) (g o pair x)
end

signature KLEISLI_ARROW_EXCEPTION =
sig
  structure K : KLEISLI
  include ARROW_EXCEPTION
  where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) K.kleisli
end

functor Kleisli_Arrow_Exception(ME : MONAD_EXCEPTION_BASE) : KLEISLI_ARROW_EXCEPTION =
struct
structure AE = Kleisli_Arrow_Exception_Base(ME)
open AE
fun throw' exn _ = ME.throw exn
fun catch' f g x = ME.catch (f x) (fn _ => g x)
fun try f = catch' f (id ())
end

signature KLEISLI_ARROW_CHOICE_BASE =
sig
  structure K : KLEISLI
  include ARROW_CHOICE_BASE
  where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) K.kleisli
end

functor Kleisli_Arrow_Choice_Base(M : MONAD_BASE) : KLEISLI_ARROW_CHOICE_BASE =
struct
structure AA = Kleisli_Arrow_Apply_Base(M)
open AA
fun cases f _ (Either.Left x) = M.map Either.Left (f x)
  | cases _ g (Either.Right y) = M.map Either.Right (g y)
fun merge f _ (Either.Left x) = f x
  | merge _ g (Either.Right y) = g y
end

signature KLEISLI_ARROW_CHOICE =
sig
  structure K : KLEISLI
  include ARROW_CHOICE
  where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) K.kleisli
end

functor Kleisli_Arrow_Choice(M : MONAD_BASE) : KLEISLI_ARROW_CHOICE =
struct
structure AC = Kleisli_Arrow_Choice_Base(M)
open AC
fun opt f _ NONE = f ()
  | opt _ g (SOME x) = g x
end

functor Applicative_Arrow(A : ARROW_BASE) : APPLICATIVE_BASE =
struct
open A
type ('p1, 'a) t = ('p1, unit, 'a) cat
fun map f = comp (arr f)
fun pure x = arr (Library.K x)
fun f <*> x = comp (arr (uncurry I)) (comp (f *** x) (arr (fn b => (b, b))))
end

functor Monad_Arrow_Apply(A : ARROW_APPLY_BASE) : MONAD_BASE =
struct
structure AA = Applicative_Arrow(A)
open A AA
fun bind m f = comp app (comp (arr (fn x => (f x, ()))) m)
end
