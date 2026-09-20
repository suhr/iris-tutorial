import Iris.HeapLang

namespace GrPredicates
open Iris HeapLang

-- # Guarded Recursive Predicates

-- In the Linked List chapter, we defined a representation predicate for
-- linked lists using Rocq's Fixpoint mechanism. In this chapter, we
-- present an alternative approach to defining representation predicates,
-- which instead uses fixpoints of predicates. The high-level point to
-- notice is that we can define fixpoints of monotone functions on Iris
-- predicates, much in the same way as one can define fixpoints of
-- monotone function on Rocq predicates. Later on, we will discuss
-- different kinds of fixpoints in more detail.

section proofs
variable [HeapLangGS hlc GF]

local instance : OFE Val := OFE.ofDiscrete _
local instance (Φ : Val → IProp GF) : OFE.NonExpansive Φ := by
  refine OFE.NonExpansive.mk ?_
  intro n x₁ x₂ ex
  rw [ex]

-- As we have already seen, we can define a predicate for linked lists
-- representing a list of specific values, using Rocq's notion of fixpoint
-- for the inductive Rocq type [list val].

def is_list_of (v : Val) (xs : List Val) : IProp GF :=
  match xs with
  | [] => iprop% ⌜v = hl_val(none())⌝
  | x :: xs => iprop%
    ∃ (l : Loc),
      ⌜v = hl_val(some(#l))⌝ ∗ ∃ t, l ↦ hl_val((&x, &t)) ∗ is_list_of t xs

-- However, sometimes we don't care about the exact list and instead, we
-- only want to know that each value of the list satisfies some
-- predicate. This can be captured by using a helper predicate [all]
-- expressing that all elements of a Rocq list satisfy a predicate.
def all (xs : List Val) (Φ : Val → IProp GF) : IProp GF :=
  match xs with
  | [] => iprop% True
  | x :: xs => iprop% Φ x ∗ all xs Φ

-- Then, using [all], we can express that a value represents _some_
-- list whose elements satisfy a given predicate.
def is_list (v : Val) (Φ : Val → IProp GF) : IProp GF := iprop%
  ∃ (xs : List Val), is_list_of v xs ∗ all xs Φ

-- However, this definition is rather annoying to work with, as it
-- requires explicitly finding the list of values. Alternatively, we can
-- define the [is_list] predicate as the solution to a recursive
-- definition. This means defining a function:
--
--   [F : (A → iProp Σ) → (A → iProp Σ)]
--
-- A solution is then a function [f] satisfying [f = F f]. Solutions to
-- such equations are called fixpoints as [f] doesn't change under [F].

def is_list_pre (Φ : Val → IProp GF) (f : Val → IProp GF) (v : Val) : IProp GF := iprop%
  ⌜v = hl_val(none())⌝ ∨
    ∃ l : Loc, ⌜v = hl_val(some(#l))⌝ ∗ ∃ x t, l ↦ hl_val((&x, &t)) ∗ Φ x ∗ f t

-- Recursive definitions can have multiple fixpoints. Of these, there are
-- two special fixpoints: the least fixpoint and the greatest fixpoint.
-- The least fixpoint corresponds to an inductively defined predicate,
-- while the greatest corresponds to a coinductively defined predicate.
--
-- These solutions exist when [F] is monotone, as captured by the
-- typeclass [BiMonoPred].
instance is_list_pre_mono (Φ : Val → IProp GF) :
    BIMonoPred (is_list_pre Φ) := by
  refine BIMonoPred.mk ?_ ?_
  · iintro %Ψ1 %Ψ2 %- %- #H1 %x H2
    unfold is_list_pre
    icases H2 with (H | ⟨%l, Hx, ⟨%x', %t, Hl, HΦx, HΨ⟩⟩)
    · ileft; iframe
    · iright
      iexists l
      iframe
      iapply H1 $$ HΨ
  · -- In addition to monotonicity, we also need to prove that the
    -- resulting predicate is `time preserving' – [NonExpansive]. We will
    -- explain non-expansiveness in more detail later. In this case, it
    -- is trivial as values are discrete.
    unfold is_list_pre
    intro Ψ h
    infer_instance

-- Now that we have proved monotonicity, we can obtain the least fixed
-- point along with associated lemmas for its unfolding and an induction
-- principle.

def is_list_rec (v : Val) (Φ : Val → IProp GF) : IProp GF :=
  bi_least_fixpoint (is_list_pre Φ) v

theorem is_list_rec_unfold (v : Val) (Φ : Val → IProp GF) :
    is_list_rec v Φ ⊣⊢ is_list_pre Φ (λ v => is_list_rec v Φ) v := by
  unfold is_list_rec
  ieval (rewrite [least_fixpoint_unfold])
  isplit <;> (iintro h; iexact h)

theorem is_list_rec_ind (Φ Ψ : Val → IProp GF) :
    □ (∀ v, is_list_pre Φ Ψ v -∗ Ψ v) -∗ ∀ v, is_list_rec v Φ -∗ Ψ v := by
  unfold is_list_rec
  iapply least_fixpoint_iter

-- Of course, this new representation predicate, [is_list_rec], should be
-- equivalent to our original definition, [is_list]. We can indeed prove
-- that this is the case.
theorem is_list_rec_correct (v : Val) (Φ : Val → IProp GF) :
    is_list v Φ ⊣⊢ is_list_rec v Φ := by
  unfold is_list
  isplit
  · iintro ⟨%xs, Hv, HΦ⟩
    iinduction xs generalizing %v Hv HΦ with
    | nil =>
      isimp [is_list_of] at Hv
      isimp [is_list_rec, least_fixpoint_unfold]
      unfold is_list_pre
      ileft
      iframe
    | cons x xs ih =>
      isimp [is_list_of] at Hv
      isimp [all] at HΦ
      icases Hv with ⟨%l, Hv, ⟨%t, Hl, Ht⟩⟩
      icases HΦ with ⟨HΦx, HΦxs⟩
      isimp [is_list_rec] at ih
      isimp [is_list_rec, least_fixpoint_unfold]
      rw [is_list_pre]
      iright
      iexists l
      iframe
      iapply ih $$ Ht HΦxs
  · irevert %v
    iapply is_list_rec_ind
    iintro !> %v HΦ
    isimp [is_list_pre] at HΦ
    icases HΦ with (%Hv | ⟨%l, %Hv, ⟨%x, %t, Hl, HΦ, ⟨%xs, Ht, Hxs⟩⟩⟩)
    · iexists []
      isimp [Hv, is_list_of, all]
      itrivial
    · iexists x::xs
      isimp [Hv, is_list_of, all]
      iframe
      ipureintro
      rfl

end proofs
