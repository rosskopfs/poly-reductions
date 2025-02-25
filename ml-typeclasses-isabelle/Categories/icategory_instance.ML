(*  Title:  icategory_instance.ML
    Author: Kevin Kappelmann

Instances of indexed categories.
*)

(*Indexed Kleisli category*)
signature IKLEISLI =
sig
  structure M : IMONAD_BASE
  type ('p1, 'i, 'o, 'a, 'b) kleisli = 'a -> ('p1, 'i, 'o, 'b) M.t
end

functor IKleisli(M : IMONAD_BASE) : IKLEISLI =
struct
structure M = M
type ('p1, 'i, 'o, 'a, 'b) kleisli = 'a -> ('p1, 'i, 'o, 'b) M.t
end

signature IKLEISLI_ARROW_BASE =
sig
  structure K : IKLEISLI
  include IARROW_BASE
  where type ('p1, 'i, 'j, 'a, 'b) cat = ('p1, 'i, 'j, 'a, 'b) K.kleisli
end

signature IKLEISLI_ARROW =
sig
  structure K : IKLEISLI
  include IARROW
  where type ('p1, 'i, 'j, 'a, 'b) cat = ('p1, 'i, 'j, 'a, 'b) K.kleisli
end

signature IKLEISLI_ARROW_APPLY_BASE =
sig
  structure K : IKLEISLI
  include IARROW_APPLY_BASE
  where type ('p1, 'i, 'j, 'a, 'b) cat = ('p1, 'i, 'j, 'a, 'b) K.kleisli
end

functor IKleisli_Arrow_Apply_Base(M : IMONAD_BASE) : IKLEISLI_ARROW_APPLY_BASE =
struct

open M
structure K = IKleisli(M)
open K

type ('p1, 'i, 'j, 'a, 'b) cat = ('p1, 'i, 'j, 'a, 'b) kleisli
fun id _ = pure
local structure M = IMonad(M) open M
in
fun comp k1 k2 x = k2 x >>= k1
fun arr f = pure o f
fun k1 *** k2 = (fn (x, y) => k1 x
  >>= (fn x' => k2 y
  >>= (fn y' => pure (x', y'))))
fun app (f, x) = f x
end

end

functor IKleisli_Arrow(M : IMONAD_BASE) : IKLEISLI_ARROW =
struct

structure K = IKleisli_Arrow_Apply_Base(M)
open K

fun first f (x, y) = M.bind (f x) (rpair y #> M.pure)
fun second f (x, y) = M.bind (f y) (pair x #> M.pure)
fun (f &&& g) x = M.bind (f x) (fn y1 => M.bind (g x) (fn y2 => M.pure (y1, y2)))
fun K x _ = M.pure x
fun curry f x y = f (x, y)

end


signature IKLEISLI_ARROW_ZERO_BASE =
sig
  structure K : IKLEISLI
  include IARROW_ZERO_BASE
  where type ('p1, 'i, 'j, 'a, 'b) cat = ('p1, 'i, 'j, 'a, 'b) K.kleisli
end

functor IKleisli_Arrow_Zero(MZ : IMONAD_ZERO_BASE) : IKLEISLI_ARROW_ZERO_BASE =
struct
structure AA = IKleisli_Arrow_Apply_Base(MZ)
open AA
fun zero _ _ = MZ.zero ()
end

signature IKLEISLI_ARROW_PLUS_BASE =
sig
  structure K : IKLEISLI
  include IARROW_PLUS_BASE
  where type ('p1, 'i, 'j, 'a, 'b) cat = ('p1, 'i, 'j, 'a, 'b) K.kleisli
end

functor IKleisli_Arrow_Plus_Base(MP : IMONAD_PLUS_BASE) : IKLEISLI_ARROW_PLUS_BASE =
struct
structure AZ = IKleisli_Arrow_Zero(MP)
open AZ
fun plus f g x = MP.plus_lazy (f x) (fn _ => g x)
end

signature IKLEISLI_ARROW_OR_BASE =
sig
  structure K : IKLEISLI
  include IARROW_OR_BASE
  where type ('p1, 'i, 'j, 'a, 'b) cat = ('p1, 'i, 'j, 'a, 'b) K.kleisli
end

functor IKleisli_Arrow_Or_Base(MO : IMONAD_OR_BASE) : IKLEISLI_ARROW_OR_BASE =
struct
structure AZ = IKleisli_Arrow_Zero(MO)
open AZ
fun or f g x = MO.or_lazy (f x) (fn _ => g x)
end

signature IKLEISLI_ARROW_EXCEPTION_BASE =
sig
  structure K : IKLEISLI
  include IARROW_EXCEPTION_BASE
  where type ('p1, 'i, 'j, 'a, 'b) cat = ('p1, 'i, 'j, 'a, 'b) K.kleisli
end

functor IKleisli_Arrow_Exception_Base(ME : IMONAD_EXCEPTION_BASE) : IKLEISLI_ARROW_EXCEPTION_BASE =
struct
structure AA = IKleisli_Arrow_Apply_Base(ME)
open AA
type 'p1 exn = 'p1 ME.exn
val throw = ME.throw
fun catch f g x = ME.catch (f x) (g o pair x)
end

signature IKLEISLI_ARROW_EXCEPTION =
sig
  structure K : IKLEISLI
  include IARROW_EXCEPTION
  where type ('p1, 'i, 'j, 'a, 'b) cat = ('p1, 'i, 'j, 'a, 'b) K.kleisli
end

signature IKLEISLI_ARROW_CHOICE_BASE =
sig
  structure K : IKLEISLI
  include IARROW_CHOICE_BASE
  where type ('p1, 'i, 'j, 'a, 'b) cat = ('p1, 'i, 'j, 'a, 'b) K.kleisli
end

functor IKleisli_Arrow_Choice_Base(M : IMONAD_BASE) : IKLEISLI_ARROW_CHOICE_BASE =
struct
structure AA = IKleisli_Arrow_Apply_Base(M)
open AA
fun cases f _ (Either.Left x) = M.map Either.Left (f x)
  | cases _ g (Either.Right y) = M.map Either.Right (g y)
fun merge f _ (Either.Left x) = f x
  | merge _ g (Either.Right y) = g y
end

signature IKLEISLI_ARROW_CHOICE =
sig
  structure K : IKLEISLI
  include IARROW_CHOICE
  where type ('p1, 'i, 'j, 'a, 'b) cat = ('p1, 'i, 'j, 'a, 'b) K.kleisli
end

functor IKleisli_Arrow_Choice(M : IMONAD_BASE) : IKLEISLI_ARROW_CHOICE =
struct
structure AC = IKleisli_Arrow_Choice_Base(M)
open AC
fun opt f _ NONE = f ()
  | opt _ g (SOME x) = g x
end

functor IApplicative_Arrow(A : IARROW_BASE) : IAPPLICATIVE_BASE =
struct
open A
type ('p1, 'i, 'j, 'a) t = ('p1, 'i, 'j, unit, 'a) cat
fun map f = comp (arr f)
fun pure x = arr (Library.K x)
fun f <*> x = comp (arr (uncurry I)) (comp (f *** x) (arr (fn b => (b, b))))
end

functor IMonad_Arrow_Apply(A : IARROW_APPLY_BASE) : IMONAD_BASE =
struct
structure AA = IApplicative_Arrow(A)
open A AA
fun bind m f = comp app (comp (arr (fn x => (f x, ()))) m)
end

