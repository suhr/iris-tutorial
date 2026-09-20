import Iris.HeapLang
import Iris.BI

namespace Timeless
open Iris HeapLang

-- # Timeless Propositions

-- ## Definition and Uses

section timeless
variable [HeapLangGS hlc GF]

-- A large class of propositions do not depend on time; they are either
-- always true or always false. An example is equalities; [2 + 2 = 4] is
-- always true. We call such propositions _timeless_. All pure
-- propositions are timeless, and ownership of a resource is timeless if
-- the resource comes from a resource algebra (this includes points-to
-- predicates). Further, timelessness is preserved by most connectives.
-- As a rule of thumb, a predicate is timeless if
-- - it does not contain a [▷]
-- - it does not mention an invariant
-- - it is first-order
--
-- Naively, one might assume that if [P] is timeless, then [▷ P ⊢ P].
-- However, together with Löb induction, this would actually imply that
-- [P] is [True]. Instead, the power of timeless propositions is
-- reflected in the rule: [▷ P ⊢ |={⊤}=> P], whenever [P] is timeless.
-- This rule allows us to strip laters from timeless propositions
-- whenever the goal contains a fancy update modality.
--
-- To identify timeless propositions, Iris uses the typeclass [Timeless].

theorem later_timeless_fup (P Q : IProp GF) [BI.Timeless P] :
    (P -∗ Q) ∗ ▷ P ⊢ |={⊤}=> Q := by
  iintro ⟨HPQ, HP⟩
  -- As [▷] is a modality, we can use the [iMod] tactic to strip it from
  -- our hypothesis. In this case, this is allowed as the goal contains a
  -- fancy update modality and [P] is timeless.
  imod HP
  iapply HPQ $$ HP

-- As usual, we can use the notation [">"] to invoke [iMod]. This is how we
-- will usually invoke [iMod] to strip laters. The above proof can hence
-- be shortened as follows.

theorem later_timeless_fup' (P Q : IProp GF) [BI.Timeless P] :
    (P -∗ Q) ∗ ▷ P ⊢ |={⊤}=> Q := by
  iintro ⟨HPQ, >HP⟩
  iapply HPQ $$ HP

-- We may _always_ add a fancy update modality in front of a WP
-- (concretely with the [fupd_wp] lemma), so we can also remove laters
-- from timeless propositions in our context if the goal is a weakest
-- precondition.

theorem later_store (l : Loc) (v : Val) :
    {{ ▷ (l ↦ v) }} hl(#l ← #4) {{ w, RET w; l ↦ hl_val(#4) }} := by
  iintro %Φ >Hl HΦ
  wp_store
  iapply HΦ $$ Hl

-- Since the points-to predicate is well supported, we do not actually
-- have to remove the later manually; the tactics work even when the
-- predicate has a later.

theorem later_store' (l : Loc) (v : Val) :
    {{ ▷ (l ↦ v) }} hl(#l ← #4) {{ w, RET w; l ↦ hl_val(#4) }} := by
  iintro %Φ Hl HΦ
  wp_store
  iapply HΦ $$ Hl

-- The last scenario we mention is when the goal contains a later. In
-- this case, we may remove laters from timeless hypotheses without
-- removing the later from the goal.

theorem later_timeless_strip (P Q : IProp GF) [BI.Timeless P] :
    (P -∗ ▷Q) ∗ ▷ P ⊢ ▷ Q := by
  iintro ⟨HPQ, >HP⟩
  iapply HPQ $$ HP


-- ## Timeless Propositions and Invariants

-- Timeless propositions are especially useful in connection with
-- invariants. Recall from the invariants chapter that when we open an
-- invariant, [inv N P], we only get the resources _later_, [▷P]. Often,
-- however, we require the resources now. Consider the following example.

theorem inv_timeless (l : Loc) (w : Val) (P : IProp GF) (N : Namespace) :
    {{ inv N iprop(⌜w = hl_val(#5)⌝ ∗ P) ∗ (l ↦ w) }}
      hl(cas(#l, #5, #6))
    {{ v, RET v; l ↦ hl_val(#6) }} := by
  iintro %Φ ⟨#Hinv, Hl⟩ HΦ
  -- To prove that the CAS succeeds, we need to know that [w] equals [5].
  -- Thus, we must open the invariant.
  wp_bind cmpXchg(#l, #5, #6)
  iinv Hinv with ⟨Heq, HP⟩
  -- Opening the invariant only gives us that [w] equals [5] later.
  -- However, as pure propositions are timeless, we can strip the later.
  imod Heq with %Heq
  rw [Heq]
  -- Now we can prove that the CAS succeeds.
  wp_cmpxchg_suc
  isplitl [HP]
  · iframe; itrivial
  · imodintro
    wp_pures
    imodintro
    iapply HΦ
    iframe

-- When opening invariants, we usually strip laters from timeless parts
-- of the invariant immediately.

theorem inv_timeless' (l : Loc) (w : Val) (P : IProp GF) (N : Namespace) :
    {{ inv N iprop(⌜w = hl_val(#5)⌝ ∗ P) ∗ (l ↦ w) }}
      hl(cas(#l, #5, #6))
    {{ v, RET v; l ↦ hl_val(#6) }} := by
  iintro %Φ ⟨#Hinv, Hl⟩ HΦ
  wp_bind cmpXchg(#l, #5, #6)
  -- Open the invariant, strip the later from the equality (achieved by
  -- [">"]), and rewrite with the equality (achieved by ["->"]).
  iinv Hinv with ⟨>%rfl, HP⟩
  wp_cmpxchg_suc
  isplitl [HP]
  · iframe; itrivial
  · imodintro
    wp_pures
    imodintro
    iapply HΦ
    iframe

end timeless
