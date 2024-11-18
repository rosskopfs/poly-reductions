(*  Title:  HOL_To_IMP_Minus/hol_nat_to_imp_util.ML
    Author: Kevin Kappelmann

General utilities when refining HOL to IMP programs.
*)
signature HOL_NAT_TO_IMP_UTIL =
sig
  include HAS_LOGGER
  val successors : int list -> int list

  (*turns option into a sequence; calls given function if option is NONE*)
  val seq_of_opt : (unit -> unit) -> 'a option -> 'a Seq.seq

  (* HOL-specific *)
  val mk_Trueprop : term -> term
  val dest_Trueprop : term -> term
  val cdest_Trueprop : cterm -> cterm
  val mk_eq : term * term -> term
  val dest_eq : term -> term * term
  val cdest_eq : cterm -> cterm * cterm

  (* simplifier *)
  val set_simps : Proof.context -> thm list -> Proof.context

  (* tactics *)
  val refl_tac : Proof.context -> int -> tactic
  val subst_first_tac : Proof.context -> thm list -> int -> tactic
  val simp_only_tac : Proof.context -> thm list -> int -> tactic

  (* pretty printing *)
  val pretty_prems : Proof.context -> term list -> Pretty.T
  val pretty_cprems : Proof.context -> cterm list -> Pretty.T

  (* sequence with monadic and applicative operations *)
  structure Seq :
  sig
    include SEQ
    structure A : APPLICATIVE where type ('p1, 'a) t = 'a seq
    structure M : MONAD where type ('p1, 'a) t = 'a seq
  end

  structure List :
  sig
    include LIST
    structure T_Seq : TRAVERSABLE
    where type ('p1, 'a) f = 'a list
    where type ('p1, 'a) A.t = ('p1, 'a) Seq.A.t
  end
end

structure HOL_Nat_To_IMP_Util : HOL_NAT_TO_IMP_UTIL =
struct

val logger = Logger.setup_new_logger HOL_Nat_To_IMP_Minus_base_logger "HOL_Nat_To_IMP_Util"

val successors = map (curry (op +) 1)

fun seq_of_opt _ (SOME x) = Seq.single x
  | seq_of_opt f_none NONE = (f_none (); Seq.empty)

(* HOL-specific *)
val mk_Trueprop = HOLogic.mk_Trueprop
val dest_Trueprop = HOLogic.dest_Trueprop
val cdest_Trueprop = Thm.dest_arg

val mk_eq = HOLogic.mk_eq
val dest_eq = HOLogic.dest_eq
val cdest_eq = Thm.dest_binop

(* simplifier *)
fun set_simps ctxt thms = (clear_simpset ctxt) addsimps thms

(* tactics *)
fun refl_tac ctxt = resolve_tac ctxt [@{thm refl}]

fun subst_first_tac ctxt = EqSubst.eqsubst_tac ctxt [1]
fun simp_only_tac ctxt thms = safe_simp_tac (set_simps ctxt thms)

(* pretty printing *)
fun pretty_prems ctxt = SpecCheck_Show.list (Syntax.pretty_term ctxt)
fun pretty_cprems ctxt = SpecCheck_Show.list (Syntax.pretty_term ctxt) o map Thm.term_of

structure Seq = struct
  open Seq
  structure M = Monad(Seq_Monad_Trans(Identity_Monad))
  structure A = Applicative(M)
end

structure List = struct
  open List
  structure T_Seq = Traversable(List_Traversable_Trans(Identity_Traversable(Seq.A)))
end


end
