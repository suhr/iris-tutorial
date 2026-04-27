import Iris.Algebra.IProp
import Iris.Instances.UPred
import Iris.ProofMode

open Iris

section proofs
variable (σ : BundledGFunctors)

-- # Pure Propositions
--
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
--
-- Pure propositions can be introduced using [iPureIntro]. This exits the
-- Iris Proof Mode, throwing away the spatial context and turns the
-- proposition into a Coq proposition.
theorem eq_5_5 : ⊢ (⌜5 = 5⌝ : IProp σ) := by
  ipure_intro
  rfl

-- To eliminate a pure proposition, we can use the specialization pattern
-- ["%_"]. This adds the proposition to the non-spatial context as a Coq
-- proposition.
theorem eq_elm {A} (P : A → IProp σ) (x y : A) : ⊢ (⌜x = y⌝ : IProp σ) -∗ P x -∗ P y := by
  iintro %φ px
  rw [φ]
  iexact px

-- It is quite easy to show that the propositions [⌜5 = 5⌝] and [⌜x = y⌝]
-- from above are pure. However, it can become quite burdensome for more
-- complicated Iris propositions. Fortunately, Iris has two typeclasses
-- [IntoPure] and [FromPure] that can identify pure propositions for us.
-- These are used by the [iPureIntro] tactic to identify pure
-- propositions automatically.

-- [True] is pure.
theorem true_intro : ⊢ (True : IProp σ) := by
  ipure_intro
  constructor

-- Conjunction preserves pureness.
theorem and_pure : ⊢ ⌜5 = 5⌝ ∧ (⌜8 = 8⌝ : IProp σ) := by
  ipure_intro
  exact ⟨rfl, rfl⟩

-- (** Separating conjunction preserves pureness. *)
theorem sep_pure : ⊢ ⌜5 = 5⌝ ∗ (⌜8 = 8⌝ : IProp σ) := by
  ipure_intro
  exact ⟨rfl, rfl⟩

-- Wand preserves pureness.
theorem wand_pure {A} (x y : A) : ⊢ ⌜x = y⌝ -∗ (⌜y = x⌝: IProp σ) := by
  ipure_intro
  exact Eq.symm

-- Arbitrary Iris propositions are not pure.
theorem abstr_not_pure (P : IProp σ) : ⊢ P -∗ ⌜8 = 8⌝ := by
  iintro p
  ipure_intro
  rfl

-- The pure embedding allows us to state an important property, namely
-- soundness. Soundness is proved in the [uPred_primitive.pure_soundness]
-- lemma stating: [∀ φ, (True ⊢ ⌜φ⌝) → φ]. This means that anything
-- proved inside the Iris logic is as true as anything proved in Coq.

-- [⌜_⌝] turns Coq propositions into Iris propositions, while [⊢ _] turns
-- Iris propositions into Coq propositions. These operations are not
-- inverses, but they are related.
theorem pure_adj1 (φ : Prop) : φ → ⊢ (⌜φ⌝ : IProp σ) := by
  intro h
  ipure_intro
  exact h

theorem pure_adj2 (P : IProp σ) : ⊢ ⌜⊢ P⌝ -∗ P := by
  iintro %h
  exact h

end proofs
