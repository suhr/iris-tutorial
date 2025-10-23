import Iris.Algebra.IProp
import Iris.Instances.UPred
import Iris.ProofMode

open Iris

section proofs
variable (σ : GFunctors) [IG : IsGFunctors σ]

-- ################################################################# *)
-- * Pure Propositions

-- The implementation of Iris in Coq has a unique class of propositions
-- called `pure'. This class arises from the fact that Coq propositions
-- can be embedded into the logic of Iris. Any Coq proposition [φ : Prop]
-- can be turned into an Iris proposition through the pure embedding
-- [⌜φ⌝ : iProp Σ]. This allows us to piggyback on much of the
-- functionality and theory developed for the logic of Coq. The
-- proposition [⌜φ⌝] is thus an Iris proposition, and we can use it as we
-- would any other Iris proposition.

theorem asm_pure (φ : Prop) : ⌜φ⌝ ⊢ (⌜φ⌝ : IProp σ) := by
  iintro h
  iexact h

-- A pure proposition is then any Iris proposition [P] for which there
-- exists a Coq proposition [φ], such that [P ⊣⊢ ⌜φ⌝].

-- Pure propositions can be introduced using [iPureIntro]. This exits the
-- Iris Proof Mode, throwing away the spatial context and turns the
-- proposition into a Coq proposition.
theorem eq_5_5 : ⊢ (⌜5 = 5⌝ : IProp σ) := by
  ipure_intro
  rfl

end proofs
