(*  Title:  lens.ML
    Author: Kevin Kappelmann

Lenses adopted from Haskell's fclables https://hackage.haskell.org/package/fclabels
Unlike fclabels, which uses GADTs and categories, we register lenses as indexed categories.
*)
signature LENS_BASE =
sig
  structure C : CATEGORY_BASE

  (*abstract lens datatype. The getter and modifier operations work in some
  category. The type of the value pointed to might change, thereby changing
  the type of the outer structure.*)
  type ('p1, 't, 'o, 's, 'i) lens
  type ('p1, 's, 'i) getter = ('p1, 's, 'i) C.cat
  type ('p1, 't, 'o, 's, 'i) modifier = ('p1, ('p1, 'i, 'o) C.cat * 's, 't) C.cat
  type ('p1, 's, 'i) slens = ('p1, 's, 'i, 's, 'i) lens
  type ('p1, 's, 'i) smodifier = ('p1, 's, 'i, 's, 'i) modifier

  val lens : ('p1, 's, 'i) getter -> ('p1, 't, 'o, 's, 'i) modifier -> ('p1, 't, 'o, 's, 'i) lens

  val get : ('p1, 't, 'o, 's, 'i) lens -> ('p1, 's, 'i) getter
  val modify : ('p1, 't, 'o, 's, 'i) lens -> ('p1, 't, 'o, 's, 'i) modifier

  val comp_modify : ('p1, 'o, 'u, 'i, 'j) modifier -> ('p1, 't, 'o, 's, 'i) modifier ->
    ('p1, 't, 'u, 's, 'j) modifier
  include ICATEGORY_BASE
  sharing type cat = lens
end

functor Lens_Base(AA : ARROW_APPLY) : LENS_BASE =
struct

structure A = Arrow(AA)
structure C = AA

type ('p1, 's, 'i) getter = ('p1, 's, 'i) C.cat
type ('p1, 't, 'o, 's, 'i) modifier = ('p1, ('p1, 'i, 'o) C.cat * 's, 't) C.cat
type ('p1, 's, 'i) smodifier = ('p1, 's, 'i, 's, 'i) modifier

datatype ('p1, 't, 'o, 's, 'i) lens = Lens of {
  get : ('p1, 's, 'i) getter,
  modify : ('p1, 't, 'o, 's, 'i) modifier
}
type ('p1, 's, 'i) slens = ('p1, 's, 'i, 's, 'i) lens

fun lens get modify = Lens {get = get, modify = modify}

fun get (Lens {get, ...}) = get
fun modify (Lens {modify, ...}) = modify

type ('p1, 'i, 'j, 'a, 'b) cat = ('p1, 'i, 'j, 'a, 'b) lens

fun id _ = lens (A.id ()) AA.app

fun comp_modify m1 m2 = AA.uncurry (A.curry m2 o A.curry m1)

fun comp l1 l2 =
  let
    val g1 = get l1
    val m1 = modify l1
    val g2 = get l2
    val m2 = modify l2
  in lens (A.comp g1 g2) (comp_modify m1 m2) end

end

signature LENS =
sig
  include LENS_BASE

  type ('p1, 't, 'o, 's) setter = ('p1, ('o * 's), 't) C.cat
  type ('p1, 's, 'o) ssetter = ('p1, ('o * 's), 's) C.cat

  val set_modify : ('p1, 't, 'o, 's, 'i) modifier -> ('p1, 't, 'o, 's) setter
  val set : ('p1, 't, 'o, 's, 'i) lens -> ('p1, 't, 'o, 's) setter

  val lens_get : ('p1, 's, 'i) C.cat -> ('p1, 'o, 'o, 's, 'i) lens
  val lens_mk : ('p1, 'o, 't) C.cat -> ('p1, 't, 'o, 'i, 'i) lens
  val lens_get_mk : ('p1, 's, 'i) C.cat -> ('p1, 'u, 'o) C.cat -> ('p1, 'o, 'u, 's, 'i) lens

  (*pairs*)
  val get_fst : ('p1, 's, 'i1 * 'i2) getter -> ('p1, 's, 'i1) getter
  val get_snd : ('p1, 's, 'i1 * 'i2) getter -> ('p1, 's, 'i2) getter
  val modify_fst : ('p1, 't, 'o1 * 'i2, 's, 'i1 * 'i2) modifier -> ('p1, 't, 'o1, 's, 'i1) modifier
  val modify_snd : ('p1, 't, 'i1 * 'o2, 's, 'i1 * 'i2) modifier -> ('p1, 't, 'o2, 's, 'i2) modifier
  val lens_fst : ('p1, 't, 'o1 * 'i2, 's, 'i1 * 'i2) lens -> ('p1, 't, 'o1, 's, 'i1) lens
  val lens_snd : ('p1, 't, 'i1 * 'o2, 's, 'i1 * 'i2) lens -> ('p1, 't, 'o2, 's, 'i2) lens

  val modify_K : ('p1, 't, (('p1, 'a, 'o) C.cat), 's, 'i) modifier -> ('p1, 't, 'o, 's, 'i) modifier
  val lens_K : ('p1, 't, (('p1, 'a, 'o) C.cat), 's, 'i) lens -> ('p1, 't, 'o, 's, 'i) lens
end

functor Lens(structure A : ARROW; structure L : LENS_BASE sharing type L.C.cat = A.cat) : LENS =
struct

open L

type ('p1, 't, 'o, 's) setter = ('p1, ('o * 's), 't) C.cat
type ('p1, 's, 'o) ssetter = ('p1, ('o * 's), 's) C.cat

fun set_modify m = C.comp m (A.first (A.arr A.K))
fun set l = set_modify (modify l)

fun lens_get f =
  L.lens (L.id () |> L.get |> L.C.comp f) (A.second f |> L.C.comp (L.modify (L.id ())))

fun lens_mk f =
  let val id = L.id ()
  in L.lens (L.get id) (L.C.comp f (L.modify id)) end

fun lens_get_mk get modify = lens_get get |> comp (lens_mk modify)

(*pairs*)
fun get_fst f = C.comp (A.arr fst) f
fun get_snd f = C.comp (A.arr snd) f
fun modify_fst f = C.comp f (A.first (A.arr A.first))
fun modify_snd f = C.comp f (A.first (A.arr A.second))

fun lens_fst l = lens (get_fst (get l)) (modify_fst (modify l))
fun lens_snd l = lens (get_snd (get l)) (modify_snd (modify l))

local open A in
fun modify_K m = C.comp m (first (arr (C.comp (arr K))))
fun lens_K l = lens (get l) (modify_K (modify l))
end

end

signature PAIR_LENS =
sig
  include LENS_BASE
  val get_pair :
    ('p1, 's1, 'i1) getter -> ('p1, 's2, 'i2) getter -> ('p1, 's1 * 's2, 'i1 * 'i2) getter
  val modify_pair : ('p1, 's1 * 's2, 'i1 * 'i2) getter ->
    ('p1, 't1, 'o1, 's1, 'i1) modifier -> ('p1, 't2, 'o2, 's2, 'i2) modifier ->
    ('p1, 't1 * 't2, 'o1 * 'o2, 's1 * 's2, 'i1 * 'i2) modifier
  val lens_pair : ('p1, 't1, 'o1, 's1, 'i1) lens -> ('p1, 't2, 'o2, 's2, 'i2) lens ->
    ('p1, 't1 * 't2, 'o1 * 'o2, 's1 * 's2, 'i1 * 'i2) lens
end

functor Pair_Lens(
    structure A : ARROW
    structure AA : ARROW_APPLY_BASE
    sharing type AA.cat = A.cat
    structure L : LENS_BASE
    sharing type L.C.cat = A.cat
  ) : PAIR_LENS =
struct

open L

local structure SC = Semi_Category(A) open SC A
in
fun get_pair g1 g2 = g1 *** g2

fun modify_pair g m1 m2 =
  arr (fn (f, x) => ((f, x), x))
  >>> first (second g >>> AA.app >>> arr (SArrow_Apply.*** (K #> pair, K #> pair)))
  >>> arr (uncurry SArrow_Apply.***)
  >>> (m1 *** m2)

fun lens_pair l1 l2 =
  let val g = get_pair (L.get l1) (L.get l2)
  in L.lens g (modify_pair g (L.modify l1) (L.modify l2)) end
end

end

signature LENS_APP =
sig
  include LENS
  val get_app : 'a -> ('p1, 's, (('p1, 'a, 'i) C.cat)) getter -> ('p1, 's, 'i) getter
  val modify_app : 'a -> ('p1, 't, 'o, 's, (('p1, 'a, 'i) C.cat)) modifier ->
    ('p1, 't, 'o, 's, 'i) modifier
  val lens_app : 'a -> ('p1, 't, 'o, 's, (('p1, 'a, 'i) C.cat)) lens -> ('p1, 't, 'o, 's, 'i) lens

  val modify_app_K : 'a -> ('p1, 't, (('p1, 'b, 'o) C.cat), 's, (('p1, 'a, 'i) C.cat)) modifier ->
    ('p1, 't, 'o, 's, 'i) modifier
  val lens_app_K : 'a -> ('p1, 't, (('p1, 'b, 'o) C.cat), 's, (('p1, 'a, 'i) C.cat)) lens ->
    ('p1, 't, 'o, 's, 'i) lens
end

functor Lens_App(
    structure A : ARROW
    structure AA : ARROW_APPLY
    sharing type AA.cat = A.cat
    structure L : LENS
    sharing type L.C.cat = A.cat
  ) : LENS_APP =
struct

open L

local structure SC = Semi_Category(A) open SC A
in
fun get_app x = C.comp (AA.app' x)
fun modify_app x m = first (arr (fn m' => AA.app' x >>> m')) >>> m
fun lens_app x l = lens (get_app x (get l)) (modify_app x (modify l))

fun modify_app_K x m = modify_K (modify_app x m)
fun lens_app_K x l = lens_K (lens_app x l)
end

end

signature LENS_KLEISLI =
sig
  include LENS
  structure K : KLEISLI
  val get_monad : ('p1, 's, ('p1, 'i) K.M.t) getter -> ('p1, 's, 'i) getter
  val modify_monad : ('p1, 't, ('p1, 'o) K.M.t, 's, ('p1, 'i) K.M.t) modifier ->
    ('p1, 't, 'o, 's, 'i) modifier
  val lens_monad : ('p1, 't, ('p1, 'o) K.M.t, 's, ('p1, 'i) K.M.t) lens ->
    ('p1, 't, 'o, 's, 'i) lens
end

functor Lens_Kleisli(
    structure A : KLEISLI_ARROW_BASE
    structure L : LENS
    where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) A.cat
  ) : LENS_KLEISLI =
struct

open L
structure K = A.K

fun get_monad f = (fn x => K.M.bind (f x) I)
fun modify_monad f = apfst K.M.map #> f
fun lens_monad l = L.lens (get_monad (L.get l)) (modify_monad (L.modify l))

end

signature LENS_KLEISLI_EXCEPTION =
sig
  include LENS_KLEISLI
  val set_safe : ('p1, 't, 'o, 's, ('p1, 'i) K.M.t) lens -> ('p1, 't, 'o, 's) setter
end

functor Lens_Kleisli_Exception(
    structure AE : KLEISLI_ARROW_EXCEPTION
    structure L : LENS
    where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) AE.cat
  ) : LENS_KLEISLI_EXCEPTION =
struct

structure LK = Lens_Kleisli(structure A = AE; structure L = L)
open LK

local structure SC = Semi_Category(AE) structure A = Kleisli_Arrow(K.M) open SC
in
fun set_safe l = apfst (fn x => AE.catch' (K.M.map (Library.K x)) (A.K x)) #> modify l
end

end

