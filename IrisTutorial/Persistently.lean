import Iris.HeapLang
import Iris.HeapLang.Lib.Par

namespace Specifications
open Iris HeapLang Par Spawn

-- # Persistently

section persistently
variable [HeapLangGS hlc GF]

-- ## Introduction

-- In separation logic, propositions are generally not duplicable. This
-- is because resources are generally exclusive. However, resources do
-- not _have_ to be exclusive. A great example of this is `read-only
-- memory'. There is no danger in letting many threads access the same
-- location simultaneously if they can only read from it. Hence, it would
-- not make sense to require that ownership of those locations be
-- exclusive. Motivated by this, we introduce a new modality denoted the
-- persistently modality, written [□ P], for propositions [P]. The
-- proposition [□ P] describes the same resources as [P], except it does
-- not claim that the resources are exclusive – hence [□ P] can be
-- duplicated. Persistent propositions hence act like propositions in an
-- intuitionistic logic, which is why they are also sometimes referred to
-- as intuitionistic.
--
-- A proposition is persistent when [P ⊢ □ P]. That is, assuming [P], we
-- need to show that [P] does not rely on any exclusive resources.
-- Persistency is preserved by most connectives, so proving that a
-- proposition is persistent is usually a matter of showing that the
-- mentioned resources are shareable. Which resources are shareable
-- depends on the specific notions of resources being used. For the
-- resource of heaps, a location can be marked as read-only, making it
-- shareable. The associated points-to predicate hence becomes
-- persistent. We will see an example of this later.
--
-- Propositions that do not rely on resources altogether are trivially
-- persistent. We have already given those types of propositions a name:
-- _pure_. This is also why we do not have to split the non-spatial
-- context when using [iSplitL]/[iSplitR]; all pure propositions are
-- persistent, hence duplicable.
--
-- Of course, not all persistent propositions are pure (e.g. persistent
-- points-to predicates). Thus, the Iris Proof Mode provides a third
-- context just for persistent propositions, called the persistent
-- context. Pure propositions can go in all three contexts. Persistent
-- propositions can go in the spatial context or the persistent context.
-- And all other propositions are limited to the spatial context only.
-- Iris uses the typeclass [Persistent] to identify persistent
-- propositions.

theorem pers_context (P Q : IProp GF) [BI.Persistent P] : P -∗ Q -∗ P ∗ Q := by
  -- The introduction pattern ["#_"] allows us to place a persistent
  -- hypothesis into the persistent context.
  iintro #hp hq
  isplitr [hq]
  -- Notice that after splitting, both the non-spatial and persistent
  -- contexts are duplicated. In particular, [HP] is available in both
  -- subgoals.
  · iexact hp
  · iexact hq

theorem not_in_pers_context (P Q : IProp GF) [BI.Persistent P] : P -∗ Q -∗ P ∗ Q := by
  -- We introduce [HP] to the spatial context.
  iintro hp hq
  isplitr [hq]
  -- [HP] is no longer duplicated.
  · iexact hp
  · iexact hq

-- Exercise: prove that persistent propositions are duplicable.

theorem pers_dup (P : IProp GF) [BI.Persistent P] : P ⊢ P ∗ P := by
  iintro #hp
  isplitl
  · iexact hp
  · iexact hp

-- Persistent propositions satisfy a lot of nice properties simply by
-- being duplicable [P ⊢ P ∗ P]. For example, [P ∧ Q] and [P ∗ Q]
-- coincide when either [P] or [Q] is persistent. Likewise, [P → Q] and
-- [P -∗ Q] coincide when [P] is persistent.

#check BI.persistent_and_sep
#check BI.imp_wand

-- The Iris Proof Mode knows these facts and allows [iSplit] to introduce
-- [∗] when one of its arguments is persistent.


-- ## Proving Persistency

-- To prove a proposition [□ P], we must prove [P] without assuming any
-- exclusive resources. In other words, we have to throw away the spatial
-- context when proving [P].

theorem pers_intro (P : IProp GF) [BI.Persistent P] : P ∗ Q ⊢ □ P := by
  iintro ⟨#hp, hq⟩
  imodintro
  iexact hp

-- Since the only difference between [□ P] and [P] is that the former
-- does not claim the resources are exclusive, it follows that the
-- persistently modality is idempotent.

theorem pers_idemp (P : IProp GF) : □ □ P ⊣⊢ □ P := by
  isplit
  · iintro p
    -- Iris already knows that [□] is idempotent, so it automatically
    -- removes all persistently modalities from a proposition when adding
    -- it to the persistent context. One may think of all propositions in
    -- the persistent context as having an implicit [□] in front.
    iexact p
  · iintro #p
    -- Similarly, we do not have to introduce [□] before proving it.
    iexact p

-- Only propositions that are instances of the [Persistent] typeclass can
-- be added to the persistent context. As with the typeclasses for pure,
-- the [Persistent] typeclass can automatically identify most persistent
-- propositions.

theorem pers_sep (P Q : IProp GF) : □ P ∗ □ Q ⊣⊢ □ (P ∗ Q) := by
  isplit
  · -- The [Persistent] typeclass detects that [□ P ∗ □ Q] is persistent.
    iintro #hpq
    icases hpq with ⟨#hp, #hq⟩
    imodintro
    -- By default, [iFrame] will not frame propositions from the
    -- persistent context. To make it do so, we must give it the argument
    -- ["#"].
    iframe #
  · iintro ⟨#hp, #hq⟩
    iframe #

-- Persistency is preserved by quantifications.

theorem pers_all {A} (P : A → IProp GF) : (∀x, □ P x) ⊢ ∀y, P y ∗ P y := by
  iintro #hp %y
  isplitl <;> iapply hp $$ %y

-- For simple predicates, such as [myPredicate] below, the [Persistent]
-- typeclass can automatically infer that it is persistent. However, we
-- can still manually make propositions instances of [Persistent].

def MyPredicate (x : Val) : IProp GF := iprop% ⌜x = hl_val(#5)⌝

example {x : Val} : BI.Persistent (PROP := IProp GF) (MyPredicate x) := by
  -- As mentioned in the beginning of the chapter, a proposition [P] is
  -- persistent when [P ⊢ □ P]. This is almost what [Persistent] requires
  -- us to prove.
  apply BI.Persistent.mk
  -- Our actual goal is of the form [P ⊢ <pers> P]. Technically, there is
  -- a small discrepancy between [□] and [<pers>], but we will ignore
  -- that here.
  --
  -- As pure propositions are persistent, we quite easily prove this.
  unfold MyPredicate
  iintro #h
  imodintro
  iexact h

-- Iris is quite smart, so we do not have to spell out the proof.
example {x : Val} : BI.Persistent (PROP := IProp GF) (MyPredicate x) := by
  unfold MyPredicate
  infer_instance

-- For more complicated predicates, such as ones defined as a fixpoint,
-- [Persistent] cannot automatically infer its persistence. The following
-- predicate asserts that all values in a given list are equal to [5].

def MyPredFix : (xs : List Val) → IProp GF
| [] => iprop(True)
| x :: xs => iprop(⌜x = hl_val(#5)⌝ ∗ MyPredFix xs)

-- This predicate only consists of pure propositions, so it should of
-- course be persistent, but when we try to add it to the persistent
-- context, Iris complains that it is not `intuitionistic' (i.e.
-- persistent).
--
-- example (x : Val) (xs : List Val) :
--     ⊢@{IProp GF} MyPredFix (x :: xs) -∗ ⌜x = hl_val(#5)⌝ ∗ MyPredFix (x :: xs) := by
--   iintro #h

-- For such predicates, we have to prove that it is persistent manually,
-- as we did for [myPredicate] above.

local instance {xs : List Val} : BI.Persistent (PROP := IProp GF) (MyPredFix xs) := by
  -- We prove it by induction in [xs].
  induction xs with
  | nil =>
    -- [True] is persistent
    unfold MyPredFix
    infer_instance
  | cons x xs ih =>
    -- By IH, [myPredFix xs'] is persistent. As ⌜x = #5⌝ is also persistent,
    -- it follows that [myPredFix (x :: xs')] is persistent.
    unfold MyPredFix
    infer_instance

-- Iris now recognises [myPredFix] as persistent.

theorem first_is_5 (x : Val) (xs : List Val) :
    ⊢@{IProp GF} MyPredFix (x :: xs) -∗ ⌜x = hl_val(#5)⌝ ∗ MyPredFix (x :: xs) := by
  iintro #h
  -- [iPoseProof] is similar to [iDestruct], but it does not throw away
  -- the hypothesis being destructed, if it is persistent.
  -- PORTING: iris-lean does not support unfolding in icases
  ihave hh := h
  iunfold MyPredFix in hh
  icases hh with ⟨hx, _⟩
  iframe #

-- ## Examples of Persistent Propositions

-- Thus far, the only basic persistent propositions we have seen are pure
-- propositions, such as equalities. In this section, we introduce two
-- additional examples of persistent propositions: Hoare triples and
-- persistent points-to predicates.

-- ### Hoare Triples

-- All Hoare triples are persistent. This probably does not come as a
-- surprise if the reader recalls how we defined Hoare triples in the
-- [specifications] chapter. As a reminder, here is the definition again.
--
--     [□( ∀ Φ, P -∗ ▷ (∀ r0 .. rn, Q -∗ Φ v) -∗ WP e {{v, Φ v }})]
--
-- The outermost part of the definition is the persistently modality! As
-- such, Hoare triples can be duplicated and reused.
--
-- Intuitively, we should also expect Hoare triples to be persistent. A
-- Hoare triple [{{{ P }}} e {{{ Φ }}}] does not actually claim ownership
-- of any resources; it merely states that _if_ we own the resources
-- described by [P], then we can safely run [e], and we get the resources
-- described by [Φ] in case of termination. Of course, if we can get
-- ownership of the resources described by [P] multiple times, we should
-- be able to run [e] multiple times.
--
-- As an example, consider a function [counter], which is parametrised
-- by an increment function.

def counter (inc : Val) : Exp := hl%
  let c := ref(#0);
  &inc c;
  &inc c;
  !c

theorem counter_spec (inc : Val) :
    {{
      ∀ (l : Loc) (z : Int),
        {{ l ↦ hl_val(#z) }} hl(&inc #l) {{ v, RET v; l ↦ hl_val(#(z + (1 : Int))) }}
    }}
      (counter inc)
    {{ v, RET v; ⌜v = hl_val(#2)⌝ }} := by
  iintro %Φ #H h2
  unfold counter
  wp_alloc l with Hl
  wp_pures
  wp_bind &inc #l
  iapply H $$ %l %_ Hl
  iintro !> %v Hl
  wp_pures
  wp_bind &inc #l
  iapply H $$ %l %_ Hl
  iintro !> %v Hl
  wp_load
  imodintro
  iapply h2
  itrivial

--- ### Persistent Points-to

-- variable [SpawnG GF]

-- The resource of heaps is more sophisticated than what we have been
-- letting on. The general shape of a points-to predicate is actually
-- [l ↦ dq v], where [dq] is a `discarded fraction'. We return to the
-- `discarded' part momentarily, but for now, we assume that [dq] is a
-- fraction in the interval (0; 1]. The predicate [l ↦ v] is a special
-- case where the fraction [dq] is [1]. The basic idea is that points-to
-- predicates can be split up and recombined, allowing ownership of
-- points-to predicates to be shared.

theorem pt_split (l : Loc) (v : Val) :
    l ↦ v ⊣⊢ l ↦{.own (.half 1)} v ∗ l ↦{.own (.half 1)} v := by
  isplit
  · iintro Hl
    icases Hl with ⟨Hl1, Hl2⟩
    iframe
  · iintro ⟨Hl1, Hl2⟩
    icombine Hl1 Hl2 as Hl
    iexact Hl

-- Crucially, a store operation can only take place if the _entire_
-- fraction is owned, i.e. [dq = 1]. However, load operations can occur
-- for any fraction.

-- theorem only_read (l : Loc) (v : Val) :
--     {{ l ↦ v }} hl(#l ← #2; !#l; #l ← #3) {{ w, RET w; l ↦ hl_val(#3) }} := by
--   iintro %Φ Hl HΦ
--   wp_store
--   -- Throw away half of the points-to predicate.
--   icases Hl with ⟨Hl1, _⟩
--   -- We can still load.
--   wp_load
--   wp_seq
--   -- But we can no longer update the pointer.
--   fail_if_success wp_store
--   sorry

-- Fractional points-to predicates are especially useful in scenarios
-- where a location is read by multiple threads in parallel but later
-- only used by a single thread.

def par_read_write (l : Loc) : Exp := hl%
  let r := (!#l ‖ !#l);
  #l ← #5

theorem par_read_write_spec [SpawnG GF] (l : Loc) (v : Val) :
    {{ l ↦ v }}
      (par_read_write l)
    {{ RET hl_val(#()); l ↦ hl_val(#5) }} := by
  iintro %Φ ⟨Hl1, Hl2⟩ HΦ
  unfold par_read_write
  -- The idea is to give each thread half of the points-to predicate and
  -- assert that both will return their halves afterwards.
  let t_post (w : Val) := iprop(⌜w = v⌝ ∗ l ↦{.own (.half 1)} v)
  wp_pures
  wp_bind &par _ _
  iapply wp_par t_post t_post $$ [Hl1] [Hl2]
  -- Each thread has a fraction of the points-to predicate, so both can
  -- perform the load.
  · unfold t_post
    wp_load
    imodintro
    iframe
    itrivial
  · unfold t_post
    wp_load
    imodintro
    iframe
    itrivial
  -- The threads return their fractions.
  unfold t_post
  iintro %v1 %v2 ⟨⟨%hv1, h1⟩, ⟨%hv2, h2⟩⟩ !>
  wp_pures
  -- We combine them, allowing us to perform the store.
  icombine h1 h2 as h
  wp_store
  imodintro
  iapply HΦ $$ h

-- Let us now turn to the `discarded' part. If one owns a fraction of a
-- points-to predicate, one can decide to _discard_ the fraction. This
-- means that it is no longer possible to recombine points-to predicates
-- to get the full fraction. As such, the value in the points-to
-- predicate can never be changed again – the location has become
-- read-only. We write [l ↦□ v] for a points-to predicate whose fraction
-- has been discarded. As the [□] suggests, this predicate is persistent.
-- Persistent points-to predicates are great if your program has a
-- read-only location, as it becomes trivial to give all threads access
-- to the associated points-to predicate, and it ensures that no thread
-- can sneakily update the location.
--
-- The [pointsto_persist] lemma asserts that we can update any points-to
-- predicate [l ↦{dq} v] into a persistent one [l ↦□ v].

#check pointsTo_persist

-- There are some caveats as to when we can discard fractions; the
-- proposition [P ==∗ Q] is equivalent to [P -∗ (|==> Q)], where [|==>]
-- is the update modality, the details of which we defer to later. For
-- now, we remark that the [iMod] tactic can remove the update modality
-- in many cases. For instance, if the goal is a weakest precondition.

theorem pt_persist (l : Loc) (v : Val) : ⊢
    l ↦ v -∗ WP hl(!#l) {{ w , ⌜w = v⌝ ∗ l ↦{.discard} v }} := by
  iintro Hl
  imod pointsTo_persist $$ Hl with Hl
  wp_load
  imodintro
  iframe
  itrivial

-- Exercise: finish the proof of the [par_read_spec] specification.

def par_read : Exp := hl%
  let l := ref(#7);
  let r := (!l + #14) ‖ (!l * #3);
  fst(r) + snd(r)

theorem par_read_spec [SpawnG GF] :
    {{ (True : IProp GF) }} par_read {{ v, RET v; ⌜v = hl_val(#42)⌝ }} := by
  iintro %Φ x HΦ {x}
  unfold par_read
  -- Both threads have the same postcondition, [t_post].
  let t_post (v : Val): IProp GF := iprop(⌜v = hl_val(#21)⌝)
  wp_alloc l with Hl
  imod pointsTo_persist $$ Hl with #Hl
  wp_pures
  wp_bind &par _ _
  iapply wp_par t_post t_post $$ [Hl] [Hl]
  · wp_load
    wp_pures
    imodintro
    itrivial
  · wp_load
    wp_pures
    imodintro
    itrivial
  unfold t_post
  iintro %v1 %v2 ⟨%hv1, %hv2⟩ !>
  isimp [hv1, hv2]
  wp_pures
  imodintro
  iapply HΦ
  itrivial

end persistently
