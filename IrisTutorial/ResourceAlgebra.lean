import Iris.HeapLang
import Iris.HeapLang.Lib.Spawn
import Iris.Algebra.CMRA
import Iris.Algebra.DFrac
import Iris.Algebra.Excl
import Iris.Algebra.Agree
import Iris.Algebra.Lib.DFracAgree

namespace ResourceAlgebra
open Iris HeapLang

-- # Resource Algebra

-- ## Introduction

-- The resource of heaps is a widely used notion of a resource,
-- applicable in many circumstances (pretty much every time your program
-- interacts with the heap). However, as it turns out, it is not the
-- solution to all our problems; some programs require other notions of
-- resources to be reasoned about. Instead of adding rules to the logic
-- for each of the notions of resources we can think of, we treat
-- resources uniformly – we define a fixed set of criteria that a notion
-- of resource must satisfy in order to be used in the logic. If the
-- notion satisfies those criteria, then it is a `resource algebra'
-- (often shortened to `RA'). We can then have a small handful of rules
-- for resource algebras in general, and we hence do not need to change
-- the logic every time we wish to use a new notion of a resource.
--
-- In this way, resource algebras are oblivious to the existence of Iris
-- – they exist as a separate thing. Iris then has a mechanism to embed
-- arbitrary resource algebras into the logic and reason about them. This
-- mechanism is called `ghost state', and we study it in the last section
-- of this chapter.
--
-- A small side note: in Iris, resource algebras are specialisations of
-- the more general structure `CMRA' (in particular, resource algebras
-- are `discrete' CMRAs). In turn, CMRAs are built on top of `Ordered
-- Families of Equivalences' (shortened to `OFE'). The exact details of
-- these concepts are not important for this chapter, but we mention them
-- as they appear a few times throughout the chapter. CMRAs and OFEs are
-- covered in more detail in later chapters.


-- ## Basic Concepts of Resource Algebra

-- ### Definition of Resource Algebra

-- A resource algebra consists of just a few components:
-- - A set of elements [A], called the carrier.
-- - An equivalence relation [Equiv A] on the elements of [A].
-- - An operation [Op A] on the elements of [A].
-- - A subset of elements [Valid A], called valid.
-- - A partial function [PCore A], called the core.
--
-- These components must satisfy certain properties, but before listing
-- those, let us discuss the purpose of each component.
--
-- Firstly, the elements of the carrier correspond to the resources of
-- the resource algebra.
--
-- Secondly, the equivalence relation, written [x ≡ y] for resources
-- [x, y ∈ A], tells us which resources are considered equivalent.
--
-- Thirdly, the operation, written [x ⋅ y] for resources [x, y ∈ A],
-- shows us how to combine resources.
--
-- Fourthly, we distinguish between valid and invalid resources, writing
-- [✓ x] to denote that [x] is valid. Intuitively, validity captures that
-- the combination of some resources should not be allowed. In the logic,
-- if we combine two valid resources and their combination is invalid,
-- then we will be able to derive falsehood.
--
-- Finally, the core, written [pcore x] for a resource [x], is a partial
-- function which extracts exactly the _shareable_ part of a resource. We
-- handle partiality in Rocq by letting the core return an option. We
-- write [pcore x = some y] to mean that the shareable part of resource
-- [x] is [y]. Similarly, we write [pcore x = none] to mean that [x] has
-- no shareable part. For resources [x] that are entirely shareable, we
-- have that [pcore x = some x].
--
-- Having discussed the purpose of each of the components, we are now
-- ready to see which properties we impose on them. In Iris, all resource
-- algebras are records in the shape described by [RAMixin]. This
-- structure describes the properties the components should satisfy.

#print CMRA

-- For convenience, we include the definition of [RAMixin] here as well.
--
-- [[
-- Record RAMixin A `{Equiv A, CMRA.pcore A, Op A, Valid A} := {
--   (* setoids *)
--   ra_op_proper (x : A) : Proper ((≡) ==> (≡)) (op x);
--   ra_core_proper (x y : A) cx :
--     x ≡ y → CMRA.pcore x = some cx → ∃ cy, CMRA.pcore y = some cy ∧ cx ≡ cy;
--   ra_validN_proper : Proper ((≡@{A}) ==> impl) valid;
--   (* monoid *)
--   ra_assoc : Assoc (≡@{A}) (⋅);
--   ra_comm : Comm (≡@{A}) (⋅);
--   ra_pcore_l (x : A) cx : CMRA.pcore x = some cx → cx ⋅ x ≡ x;
--   ra_pcore_idemp (x : A) cx : CMRA.pcore x = some cx → CMRA.pcore cx ≡ some cx;
--   ra_pcore_mono (x y : A) cx :
--     x ≼ y → CMRA.pcore x = some cx → ∃ cy, CMRA.pcore y = some cy ∧ cx ≼ cy;
--   ra_valid_op_l (x y : A) : ✓ (x ⋅ y) → ✓ x
-- }.
-- ]]
--
-- The `setoids' rules state that equivalence of elements is respected by
-- the operation, the core, and validity. For instance, [ra_op_proper]
-- expresses that, if [y ≡ z], then [x ⋅ y ≡ x ⋅ z], for all [x].
--
-- The fields [ra_assoc] and [ra_comm] assert that the operation [⋅]
-- should be associative and commutative. This, in effect, makes [A] a
-- commutative semigroup, which means that we can make all resource
-- algebras a preorder through the extension order, written [x ≼ y]. The
-- extension order is defined as:
--
--       [x ≼ y = ∃z, y ≡ x ⋅ z]
--
-- Intuitively, the resource [x] is _included_ in [y], if we can express
-- [y] in terms of [x] and some [z].
--
-- The fields [ra_pcore_l] and [ra_pcore_idemp] capture the idea that the
-- core extracts the shareable part of a resource and how shareable
-- resources behave. [ra_pcore_l] expresses that including the same
-- shareable resource multiple times does not change a resource, and
-- [ra_pcore_idemp] states that invoking the core on a resource twice
-- gives the same resource as invoking the core once.
--
-- [ra_pcore_mono] captures the relationship between the core and the
-- extension order.
--
-- Finally, [ra_valid_op_l] asserts that all parts of a valid resource
-- are themselves valid.
--
-- All resource algebra satisfy the properties of [RAMixin], and when
-- creating a new resource algebra, one must show that it is an [RAMixin]
-- record. However, in this chapter, and in most real-world scenarios for
-- that matter, we will not create resource algebras from scratch. We can
-- utilise existing resource algebras and compose them to create a
-- resource algebra that suitably models our desired notion of a
-- resource. This allows us to forgo proving the properties of [RAMixin].
-- We refer to chapter [Custom Resource Algebra] for an introduction to
-- creating resource algebras from scratch.


-- ### An Example Resource Algebra : dfrac

-- That was a lot of abstract information, so let us get a bit more
-- concrete and study the definition of resource algebra through a
-- familiar example: discardable fractions (shortened to dfrac). We saw
-- discardable fractions when we introduced the persistent points-to
-- predicate in the persistently chapter. As it turns out, the resource
-- of heaps is actually composed of other resource algebras, one of which
-- is dfrac.
--
-- As dfrac is a resource algebra, it is an instance of [RAMixin].

#synth CMRA DFrac

-- As such, it has a carrier, an equivalence relation, an operation, a
-- core, and a subset of valid elements, and these satisfy the properties
-- specified in the fields of [RAMixin]. We proceed to discuss each of
-- these in turn. The full definitions of the components can be found at
--
-- <<https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/algebra/dfrac.v>>


-- #### The Carrier (the [A])

-- In dfrac, a resource is either a fraction, knowledge that a fraction
-- has been discarded, or a combination of the two.
--
-- When the resource is a fraction [Qp], we write [DfracOwn Qp]. When the
-- resource is knowledge that a fraction has been discarded, we write
-- [DfracDiscarded]. Finally, when the resource is a fraction _and_ the
-- knowledge that a fraction has been discarded, we write [DfracBoth Qp].
-- The carrier is denoted [dfrac].

#print DFrac

-- For instance, [DfracOwn (1/2)] is a resource in dfrac.
#check DFrac.own (⟨1 / 2, by grind⟩)

-- And so is knowledge of a fraction having been discarded.
#check DFrac.discard


-- #### Operation (the [Op A])

-- The operation [⋅] is defined by considering all possible combinations of
-- the three kinds of dfrac resources.

#print DFrac.op

-- For instance, if the two resources are fractions, then the operation
-- adds the fractions together.

theorem dfrac_op :
    DFrac.own ⟨1 / 2, by grind⟩ • DFrac.own ⟨1 / 4, by grind⟩ =
      .own ⟨3 / 4, by grind⟩ :=
  by
    simp [DFrac.op_own]
    grind only

theorem dfrac_op2 :
    DFrac.own ⟨2 / 3, by grind⟩ • DFrac.own ⟨2 / 3, by grind⟩ =
      .own ⟨4 / 3, by grind⟩ :=
  by
    simp [DFrac.op_own]
    grind only

-- If the resources are both knowledge that a fraction has been
-- discarded, then the operation simply returns this knowledge.

theorem dfrac_op_disc : DFrac.discard • DFrac.discard = .discard := rfl

-- If one of the resources is knowledge of a discarded fraction
-- [DfracDiscarded] and the other a fraction [DfracOwn Qp], the operation
-- turns the fraction into [DfracBoth Qp].

theorem dfrac_op_both :
    DFrac.own ⟨2 / 3, by grind⟩ • DFrac.discard = .ownDiscard ⟨2 / 3, by grind⟩ :=
  rfl

-- Exercise: reduce the following expressions.

set_option warn.sorry false in
theorem dfrac_op_both_disc : ∃ x : DFrac,
    DFrac.ownDiscard ⟨2 / 3, by grind⟩ • DFrac.discard = x := by
  -- (exercise)
  sorry

set_option warn.sorry false in
theorem dfrac_op_frac_both : ∃ x : DFrac,
    DFrac.own ⟨1 / 4, by grind⟩ • DFrac.ownDiscard ⟨2 / 4, by grind⟩ = x := by
  -- (exercise)
  sorry

-- As dfrac is a record of type [RAMixin], we know that [⋅] must be
-- associative and commutative. We can refer to these properties through
-- record projection.

theorem dfrac_op_assoc (dq1 dq2 dq3 : DFrac) :
    (dq1 • dq2) • dq3 = dq1 • (dq2 • dq3) := by
  exact Eq.symm CMRA.assoc'

theorem dfrac_op_comm (dq1 dq2 : DFrac) : dq1 • dq2 = dq2 • dq1 :=
  CMRA.comm


-- #### Valid Elements (the [Valid A])

-- The idea with using fractions as resources is to be able to split up
-- ownership into smaller parts. As such, we let the fraction [1]
-- represent total ownership, and fractions less than [1] denote partial
-- ownership. In this way, fractions greater than [1] are nonsensical and
-- are thus not valid. Likewise for fractions smaller than or equal to
-- [0]. In other words, only fractions in the interval (0; 1] are valid.
-- Knowledge that a fraction has been discarded is also valid. The
-- function [dfrac_valid_instance] defines this formally.

#print DFrac.valid

-- Note that for [DfracBoth q], we require that [q] is _strictly_ smaller
-- than [1], reflecting that a fraction has been discarded, making it
-- impossible to have total ownership.

-- The lemma [dfrac_valid] converts a validity assertion into the
-- corresponding propositions as defined by [dfrac_valid_instance].

theorem dfrac_valid_own : ✓ (DFrac.own ⟨2 / 3, by grind⟩) := by
  simp [DFrac.valid_own]
  grind

set_option warn.sorry false in
theorem dfrac_valid_discarded : ✓ (DFrac.discard) :=
  -- (exercise)
  sorry

theorem dfrac_invalid_own :
    ¬ (✓ (DFrac.own ⟨2 / 3, by grind⟩ • DFrac.own ⟨2 / 3, by grind⟩)) := by
  simp [DFrac.op_own, DFrac.valid_own]
  grind


-- #### The Core (the [PCore A])

-- For dfrac, ownership of a fraction should be exclusive, while
-- knowledge that a fraction has been discarded should be freely
-- shareable. We manifest this desire through the definition of the core.

#print DFrac.pcore

-- That is, the core of a [DfracOwn] resource is [None].
theorem dfrac_core_own (q : Qp) : CMRA.pcore (DFrac.own q) = none := rfl

-- The core of [DfracDiscarded] is [Some DfracDiscarded].
theorem dfrac_core_discarded : CMRA.pcore (DFrac.discard) = some .discard := rfl

-- And the most interesting case, the core of a [DfracBoth] resource is
-- just [Some DfracDiscarded].
theorem dfrac_core_both (q : Qp) : CMRA.pcore (DFrac.ownDiscard q) = some .discard :=
  rfl

-- Recall that, in general, the core extracts _exactly_ the shareable
-- part of a resource. Since only knowledge of a fraction having been
-- discarded should be shareable, the image of the core should only
-- contain [DfracDiscarded]. In particular, because all resources
-- [DfracBoth q] can be written as [DfracDiscarded ⋅ DfracOwn q], the
-- core of a [DfracBoth] resource should be just the shareable part:
-- [DfracDiscarded].


-- #### The preorder (the [≼])

-- Unlike the other components, the preorder is defined for us as the
-- extension order: [x ≼ y = ∃z, y ≡ x ⋅ z]. The proposition [x ≼ y]
-- expresses that [x] is included in [y].

theorem dfrac_pre_own : DFrac.own ⟨1 / 4, by grind⟩ ≼ DFrac.own ⟨3 / 4, by grind⟩ := by
  exists DFrac.own ⟨2 / 4, by grind⟩
  simp [DFrac.op_own]
  grind

set_option warn.sorry false in
theorem dfrac_pre_disc_both : DFrac.discard ≼ DFrac.ownDiscard ⟨3 / 4, by grind⟩ :=
  -- (exercise)
  sorry

set_option warn.sorry false in
theorem dfrac_pre_own_both :
    DFrac.own ⟨2 / 4, by grind⟩ ≼ DFrac.ownDiscard ⟨3 / 4, by grind⟩ :=
  -- (exercise)
  sorry


-- ### Frame Preserving Update

-- The final core ingredient we need for resource algebra is a way to
-- update resources – resources are used to reason about programs, and
-- programs update resources. One has to be careful with how resources
-- are allowed to be updated; in Iris, only _valid_ resources can be
-- owned. It should always be the case that if we combine the resources
-- owned by all threads in the system, the resulting resource should be
-- valid. Otherwise, we could easily derive falsehood. Hence, when a
-- thread updates its resources, it must ensure that it does not
-- introduce the possibility of obtaining an invalid element. We call
-- such an update a `frame preserving update' and write [x ~~> y] to mean
-- that we can perform a frame preserving update from resource [x] to
-- resource [y]. The formal definition for this notion turns out to be
-- quite succinct:
--
--               [x ~~> y = ∀z, ✓(x ⋅ z) → ✓(y ⋅ z)]
--
-- This proposition ensures that every resource that is valid with [x] is
-- also valid with [y]. If this is the case, then it is okay to update
-- [x] to [y]. Since [z] is forall quantified, [z] also represents the
-- resource we get by combining the resources from all other threads.
-- That is to say, [x ~~> y] ensures that if the combination of all
-- resources was valid before the update, it still is after. As [z]
-- represents all the other resources, it is called the `frame', and the
-- proposition [x ~~> y] expresses that the validity of [z] – the frame –
-- is preserved, hence `frame preserving update'.

-- Due to some technicalities, when the core is not total (i.e. the core
-- is [None] for some resources), we use a slightly more general
-- definition of the frame preserving update:
--
--               [x ~~> y = ∀mz, ✓(x ⋅? mz) → ✓(y ⋅? mz)]
--
-- The only difference is that the frame [mz] is now an option, i.e.
-- [None] or [Some z]. The operation [⋅] does not work with option
-- elements, so we use [a ⋅? mb] instead, which returns [a] if [mb] is
-- [None], and [a ⋅ b] if [mb] is [Some b].

-- To complicate matters further, the frame preserving update works for
-- CMRAs in general, not just resource algebra. Hence, the actual
-- definition of [~~>] is slightly more complex than above.

#print Update

-- However, when the CMRA is discrete (hence a resource algebra), we can
-- prove that the actual definition of [~~>] is equivalent to our
-- definition above.

#check Update.discrete

-- Further, if the core is total, it is also equivalent to our first
-- definition of the frame preserving update.

#check Update.discrete_total


-- #### Example with dfrac

-- The by far most commonly used update for dfrac resources is to discard
-- a fraction. Intuitively, such an update is frame preserving as only
-- fractions greater than [1] are considered invalid. If a thread
-- discards its fraction, the sum total from all threads will only
-- decrease. So if the frame was valid before (i.e. less than or equal to
-- [1]), it will remain valid after discarding. As such, we can always
-- discard fractions.

#check DFrac.update_discard

example : DFrac.own ⟨2 / 3, by grind⟩ ~~> DFrac.discard := DFrac.update_discard

example : DFrac.discard ~~> DFrac.discard := DFrac.update_discard

-- Recall that, in the persistently chapter, we used the
-- [pointsto_persist] lemma to make points-to predicates persistent.
-- Looking deep under the hood, [pointsto_persist] actually uses
-- [dfrac_discard_update] to discard the dfrac in [l ↦{dq} v].

-- Of course, there are also other frame preserving updates for dfrac.
-- However, these we must prove manually. Since the core of dfrac is not
-- total, we can only use the definition of frame preserving update with
-- the frame being an option ([cmra_discrete_update]).
--
-- For example, a trivial update is the identity.

theorem dfrac_update_ident (dq : DFrac) : dq ~~> dq := Update.id

-- We can also update a fraction by decreasing it.

theorem dfrac_update_own_own :
    DFrac.own ⟨3 / 4, by grind⟩ ~~> DFrac.own ⟨1 / 4, by grind⟩ := by
  apply Update.discrete.mpr
  intro mz h
  match mz with
  | .none =>
    simp [CMRA.op?, DFrac.valid_own] at ⊢
    grind
  | .some (.own q) =>
    simp [CMRA.op?, DFrac.op_own, DFrac.valid_own] at h ⊢
    grind
  | .some (.discard) =>
    simp [CMRA.op?, CMRA.op, DFrac.op, CMRA.Valid, DFrac.valid]
    grind
  | .some (.ownDiscard q) =>
    simp [CMRA.op?, CMRA.op, DFrac.op, CMRA.Valid, DFrac.valid] at h ⊢
    grind

-- We can additionally get [DfracDiscarded] when updating a fraction by
-- decreasing it.
-- Exercise: finish the proof of the example.
-- Hint: use [cmra_discrete_update] to rewrite [dfrac_discard_update].

set_option warn.sorry false in
theorem dfrac_update_own_both :
    DFrac.own ⟨3 / 4, by grind⟩ ~~> DFrac.ownDiscard ⟨1 / 4, by grind⟩ := by
  -- (exercise)
  sorry


-- ## Example Resource Algebra

-- We have been using dfrac as a running example to introduce the
-- concepts of resource algebra. While dfrac has some use cases on its
-- own, it is especially useful when composed with other resource algebra
-- (e.g. it is used to define the points-to predicate). Hence, in this
-- section, we will introduce some often-used resource algebras.
--
-- Unlike dfrac, the resource algebras we study in this section are
-- parametrised by other resource algebras (or OFEs, or CMRAs). This
-- makes them generic, enabling us to use them to define more complex
-- resource algebras.
--
-- The collection of resource algebras we present here is by no means
-- exhaustive – Iris ships with a myriad of useful resource algebras,
-- which can be found at
--
-- <<https://gitlab.mpi-sws.org/iris/iris/-/tree/master/iris/algebra>>.


-- ### Exclusive

section exclusive

-- Our first example is the `exclusive' resource algebra. The key idea is
-- that it makes all combinations of resources from some resource algebra
-- invalid. The exclusive RA is actually parametrised by an OFE, but
-- since all resource algebras are OFEs, the exclusive RA also works for
-- resource algebras.
--
-- Below, we let [A] be some OFE, but we may think of it as being the
-- carrier for some resource algebra.

variable [OFE α]

-- The carrier of the exclusive RA, [excl], is the same as the carrier of
-- the underlying resource algebra with the addition of a bottom element,
-- denoted [ExclInvalid].

#print Excl

-- The core is always undefined (nothing is shareable).

theorem excl_core (ea : Excl α) : CMRA.pcore ea = none := rfl

-- Crucially, all elements except [ExclInvalid] are valid.

theorem excl_valid (a : α) : ✓ (Excl.excl a) := ⟨⟩

theorem excl_bot_invalid : ¬ ✓ (.invalid : Excl α) := id

-- And the combination of any two elements gives the invalid [ExclInvalid].

theorem excl_op (ea eb : Excl α) : ea • eb = .invalid := rfl

-- Let us return to our beloved dfrac. While the operation for dfrac adds
-- two dfrac fractions together, the operation for two _exclusive_ dfrac
-- fractions simply results in [ExclInvalid].

example :
    Excl.excl (DFrac.own ⟨1 / 4, by grind⟩) •
      Excl.excl (DFrac.own ⟨2 / 4, by grind⟩) = .invalid :=
  rfl

end exclusive

-- So how is this resource algebra useful? While it is a key component in
-- many fairly complex resource algebras, it has a super simple yet
-- extremely practical use case. Together with the OFE [unitO], we can
-- create the resource algebra of `tokens'.

section token

-- A token is then simply an exclusive unit.
def tok := Excl.excl ()

-- The token is valid...
theorem token_valid : ✓ tok := ⟨⟩

-- ... but having the token twice gives the bottom element...
theorem token_token_bot : tok • tok = Excl.invalid := rfl

-- ... which is invalid.
theorem token_exclusive : ¬ ✓ (tok • tok) := id

-- As only valid resources can be owned in Iris, and the contribution
-- from all threads should yield a valid resource, we know that only a
-- single token can be owned at any one time. Among others, this resource
-- algebra is useful to reason about programs whose correctness rely on
-- only one thread accessing some critical section of memory at a time.
-- We will see concrete examples of this in later chapters.

end token


-- ### Agree

section agree

-- The agree construction is parametrised by an ofe [A] (again, think
-- carrier of resource algebra), and all it cares about is whether two
-- resources are equivalent. That is, whether they _agree_. As such, the
-- carrier of agree is the same as the carrier of the underlying resource
-- algebra, and all resources in [agree A] are valid – regardless of
-- their validity in the original resource algebra.

variable [OFE α]

theorem agree_valid (a : α) : ✓ (toAgree a) := by
  exact Agree.toAgree_valid

-- Additionally, we make all resources shareable.

theorem agree_core (a : Agree α) : CMRA.pcore a = some a := by
  rfl

-- The key idea is that only resources that are equivalent in the
-- original resource algebra can be combined.

#check toAgree_op_valid_iff_eq

-- For instance, if the resources are dfrac fractions, the fractions have
-- to be the same.

theorem agree_dfrac :
    ✓ toAgree (DFrac.own ⟨1 / 2, by grind⟩) • toAgree (DFrac.own ⟨2 / 4, by grind⟩) := by
  apply toAgree_op_valid_iff_eq.mpr
  grind

theorem disagree_dfrac :
    ¬ ✓ toAgree (DFrac.own ⟨1 / 4, by grind⟩) • toAgree (DFrac.own ⟨2 / 4, by grind⟩) := by
  refine ?_ ∘ toAgree_op_valid_iff_eq.mp
  grind

-- If the composition of two elements is valid, it hence just amounts to
-- composing a resource with itself. Since we only care about which
-- resources are equivalent, we define composition as to be idempotent.

#check Agree.idemp

theorem agree_dfrac_op :
    toAgree (DFrac.own ⟨1 / 2, by grind⟩) • toAgree (DFrac.own ⟨2 / 4, by grind⟩) =
    toAgree (DFrac.own ⟨1 / 2, by grind⟩) := by
  have : DFrac.own ⟨1 / 2, by grind⟩ = DFrac.own ⟨2 / 4, by grind⟩ :=
    by grind
  simp [this, Agree.idemp]

-- As a result, if a composition is valid, the result is simply one of
-- the two (equivalent) resources.

set_option warn.sorry false in
theorem agree_valid_opL (a b : α) : ✓ (toAgree a • toAgree b) →
    toAgree a • toAgree b = toAgree a := by
  -- (exercise)
  sorry

-- Due to idempotency and the fact that the combination of equivalent
-- resources is valid, we get that the extension order coincides with
-- equivalence.

set_option warn.sorry false in
theorem to_agree_included (a b : α) :
    toAgree a ≼ toAgree b ↔ a = b := by
  -- (exercise)
  sorry

-- The usefulness of the agree construction is demonstrated by the fact
-- that it is used to define the resource of heaps. The inclusion of the
-- agree RA allows us to conclude that if we have two points-to
-- predicates for the same location, [l ↦{dq1} v1] and [l ↦{dq2} v2],
-- then they _agree_ on the value stored at the location: [v1 = v2].

#check pointsTo_agree

end agree


-- ### Product

section product

-- While Iris supports reasoning about multiple different notions of
-- resources simultaneously, it is sometimes useful to combine them at
-- the level of resource algebras. To this end, we have the `product'
-- resource algebra, [prodR], which is parametrised by _two_ CMRAs.

variable [CMRA A] [CMRA B]

-- Elements of the product resource algebra are pairs of elements from
-- [A] and [B].

variable {a : A} {b : B}

#check ((a, b) : A × B)

-- For the product RA, the two CMRAs are largely treated in parallel. For
-- instance, pairs are composed component-wise.

#print Prod.op

-- A pair is valid exactly when its components are valid.

#print Prod.Valid

-- When the core is defined for both of the components of a pair, the
-- core of the pair is simply the core of the components.

theorem pair_pcore_some (ca : A) (cb : B) :
    CMRA.pcore a = some ca →
    CMRA.pcore b = some cb →
    CMRA.pcore (a, b) = some (ca, cb) := by
  intro ica icb
  simp [CMRA.pcore, Prod.pcore, ica, icb]

-- However, if the core of just one of the components is undefined, then
-- the core of the pair is also undefined.

theorem pair_pcore_dfrac : CMRA.pcore (DFrac.own ⟨1 / 2, by grind⟩, b) = none := by
  simp [CMRA.pcore, Prod.pcore, DFrac.pcore]

-- The product RA is often used in conjunction with dfrac and agree, with
-- the first component being a dfrac and the second being an element of
-- some resource algebra wrapped in agree. This pattern is common enough
-- that it has been added to Iris' library of resource algebras.

#synth CMRA (DFrac × Agree A)

-- This construction is a simple way to make the resources of some
-- resource algebra [A] shareable between threads in a safe way.

end product


-- ## Ghost State

section ghost

set_option linter.unusedSectionVars false

-- In the previous sections, we duly studied the key concepts of resource
-- algebras and a handful of basic examples. It is due time we put all
-- that theory to use. In this section, we will see how to use resource
-- algebras inside the Iris logic.

-- ## Accessing Resource Algebras in Rocq

-- To use a resource algebra inside the Iris logic, we first need to make
-- the resource algebra available. As we have stated before, propositions
-- in Iris have type [iProp Σ]. The [Σ] can be thought of as a global
-- list of resource algebras that are available in the logic. The [Σ] is
-- always universally quantified to enable composition of proofs.
-- However, we may put _restrictions_ on [Σ] to specify that the list
-- must contain some specific resource algebra of our choosing. The
-- typeclass [inG Σ R] expresses that the resource algebra [R] is in the
-- [G]lobal list of resource algebras [Σ]. If we add this to the Rocq
-- Context, then we may assume that [Σ] contains [R], allowing us to use
-- [R] inside the logic.
--
-- For instance, let us say that we want to use the resource algebra of
-- exclusive unit. The resource algebra for exclusive is denoted
-- [exclR], and we here instantiate it with the [unitO] OFE.

variable [e_excl : ElemG GF (constOF (Excl Unit))]

-- Similarly, if we want to use the resource algebra of discardable
-- fractions, we assert that [Σ] must contain [dfracR] – the name of the
-- resource algebra in Rocq.

variable [e_dfrac : ElemG GF (constOF DFrac)]

-- Libraries often bundle the resource algebras they need into their own
-- typeclasses so that they do not have to expose the details of the
-- resource algebras to clients. For instance, the [spawn] library
-- includes its required resource algebras in the [spawnG Σ] typeclass.
-- As such, adding this to the Rocq Context makes the resource algebras
-- required by [spawn] available.

variable [Spawn.SpawnG GF]

-- Similarly, the [heapGS Σ] typeclass asserts that the resource of heaps
-- is present in [Σ].

variable [heapGS : HeapLangGS hlc GF]

-- For additional information, please consult:
--
-- <<https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/resource_algebras.md>>


-- ### Ownership of Resources

-- Now that we have ensured that [Σ] contains our desired resource
-- algebras, we can start using them inside the logic. Iris provides
-- exactly one way of embedding a resource [r] from some resource algebra
-- [R] into the logic: the proposition [own γ r] asserts _ownership_ of
-- the resource [r] in an instance of the resource algebra [R] named [γ].
-- That is to say, in Iris, once we have added an [R] to [Σ], we may
-- create multiple instances of [R] so that the same resource in [R] may
-- be owned multiple times. To distinguish between instances, we use
-- `ghost names' (sometimes also called `ghost variables' or `ghost
-- locations'), which is usually written with a lower-case gamma: [γ].
--
-- For instance, as we have added [(exclR unitO)] to [Σ], we can define
-- tokens as ownership of the single valid resource in the resource
-- algebra.

abbrev token (γ : GName) := iOwn (E := e_excl) γ (Excl.excl ())

-- We can have multiple tokens, each of which is associated with its own
-- instance of the resource algebra. In this way, the [γ] serves as a
-- name for the token.

-- Looking under the hood, the points-to predicate [l ↦ v] is also
-- defined in terms of [own]. That is, [l ↦ v] is just notation denoting
-- ownership of a resource in the resource of heaps! But where is the
-- ghost name [γ]? When adding the resource of heaps to [Σ], we do it
-- with the [heapGS Σ] typeclass. Here, the [S] stands for `singleton'
-- and signifies that only _one_ instance of the resource of heaps
-- exists. As such, we do not need ghost names to distinguish between
-- instances.

-- If one owns multiple resources from the same instance of a resource
-- algebra, then these resources may be combined with the [iCombine]
-- tactic. Conversely, if one owns a resource that is composed of other
-- resources, one may split up the ownership into the constituent
-- resources with [iDestruct].
--
-- That is, we have the following rule:
--
--     [own γ a ∗ own γ b ⊣⊢ own γ (a ⋅ b)]
--
-- Let's see an example of this.

theorem own_op_dfrac (γ : GName) : ⊢@{IProp GF}
    iOwn (E := e_dfrac) γ (DFrac.own .quarter) ∗
      iOwn (E := e_dfrac) γ (DFrac.ownDiscard .quarter) ∗-∗
    iOwn (E := e_dfrac) γ (DFrac.ownDiscard (.half 1)) := by
  have : DFrac.own .quarter • DFrac.ownDiscard .quarter = DFrac.ownDiscard (.half 1) := by
    simp [CMRA.op, DFrac.op]; grind
  simp [iOwn_op.to_eq.symm, this, BI.wandIff_refl]

-- In Iris, all owned resources are valid. This is captured by the
-- [own_valid] lemma.

#check iOwn_valid_r

-- We can use the [own_valid] lemma to prove that token ownership is
-- exclusive.

theorem own_token_exclusive (γ : GName) : token γ ∗ token γ ⊢@{IProp GF} False := by
  iintro ⟨h1, h2⟩
  icombine h1 h2 as h
  icases iOwn_valid_r $$ h with ⟨_, %h⟩
  ipureintro
  exact h

-- Validity of owned resources can also be extracted with the [iCombine]
-- tactic.

theorem own_token_exclusive' (γ : GName) :
    token γ ∗ token γ ⊢@{IProp GF} False := by
  iintro ⟨h1, h2⟩
  icombine h1 h2 as _ gives %h
  ipureintro
  exact h

-- Recall that the core extracts the shareable part of a resource. If the
-- core of some resource is itself, then that resource is freely
-- shareable – in particular, ownership of the resource is duplicable.
-- That is, if [pcore r = Some r], then [own γ r] is persistent.

theorem own_dfrac_disc_persistent (γ : GName) :
    iOwn (E := e_dfrac) γ DFrac.discard ⊢@{IProp GF}
    (iOwn (E := e_dfrac) γ DFrac.discard) ∗ (iOwn (E := e_dfrac) γ DFrac.discard) := by
  iintro #h
  iframe #

set_option warn.sorry false in
theorem own_dfrac_both_disc (γ : GName) :
    iOwn (E := e_dfrac) γ (DFrac.ownDiscard ⟨2 / 3, by grind⟩) ⊢@{IProp GF}
    (iOwn (E := e_dfrac) γ (DFrac.ownDiscard ⟨2 / 3, by grind⟩)) ∗
      (iOwn (E := e_dfrac) γ DFrac.discard) := by
  -- (exercise)
  sorry


-- ### Update Modality

-- We now know how to combine and split ownership of resources, but we
-- are missing two crucial features: allocation and updating. That is, we
-- must be able to get ownership of new resources, and we must be able to
-- update owned resources. To support these operations, Iris uses the
-- `update modality', [|==>], which we have already been exposed to in
-- previous chapters. Intuitively, the proposition [|==> P] describes the
-- resources we _could_ own after performing a frame preserving update
-- from the resources described by [P].
--
-- We may always introduce an update modality.

theorem upd_intro (P : IProp GF) : P ⊢ |==> P := by
  iintro HP
  -- As [|==>] is a modality, we can use the [iModIntro] and [iMod]
  -- tactics to work with it.
  imodintro
  iapply HP

-- We can remove an update modality from an assumption if the goal
-- contains an update modality.

theorem upd_assumption (P Q : IProp GF) : (P -∗ Q) ∗ (|==> P) ⊢ |==> Q := by
  iintro ⟨HPQ, HuP⟩
  imod HuP with HP
  imodintro
  iapply HPQ $$ HP

-- Recall that we can use [>] in an introduction pattern to invoke
-- [iMod], and [!>] to invoke [iModIntro].

theorem upd_assumption' (P Q : IProp GF) : (P -∗ Q) ∗ (|==> P) ⊢ |==> Q := by
  iintro ⟨HPQ, >HP⟩ !>
  iapply HPQ $$ HP

-- Only some goals permit removing update modalities from assumptions. In
-- the general case, we cannot strip update modalities.

set_option warn.sorry false in
theorem upd_assumption_fail (P Q : IProp GF) : (P -∗ Q) ∗ (|==> P) ⊢ Q := by
  iintro ⟨HPQ, HuP⟩
  fail_if_success imod HuP with HP
  sorry

-- Notably, we can remove update modalities if the goal is a weakest
-- precondition.

theorem upd_wp (P : IProp GF) : (|==> P) ⊢ WP hl(#4 + #2) {{ _v, P }} := by
  iintro >HP
  wp_pures
  iexact HP

-- Exercise: Prove that updating our resources two times in a row is
-- equivalent to just updating them once.

set_option warn.sorry false in
theorem upd_idemp (P : IProp GF) : (|==> |==> P) ⊢ |==> P := by
  -- (exercise)
  sorry


-- ### Allocation and Updates

-- New resources are created by making a new instance of some resource
-- algebra. This is captured by the [own_alloc] lemma.

#check iOwn_alloc

-- That is, if we have some resource algebra [A] and wish to create and
-- get ownership of resource [a] in [A], then, as long as [a] is valid,
-- we may update our resources to get ownership of [a] in a _fresh_
-- instance of [A], identified by a fresh ghost name [γ].
--
-- For instance, we can always create new tokens.

theorem token_alloc : ⊢@{IProp GF} |==> ∃ γ, token γ := by
  iapply iOwn_alloc
  apply token_valid

-- We can also create new, total dfracs.

set_option warn.sorry false in
theorem dfrac_alloc_one : ⊢@{IProp GF} |==> ∃ γ, iOwn (E := e_dfrac) γ (DFrac.own 1) :=
  -- (exercise)
  sorry

-- After having allocated new resources, we may update them using the
-- [own_update] lemma.

#check iOwn_update

-- Essentially, if we own resource [a], then we may update our resources
-- to get ownership of resource [a'], as long as we can do a frame
-- preserving update from [a] to [a'].
--
-- For example, since we can do a frame preserving update from any dfrac
-- element to [DfracDiscarded], we can always update ownership of any
-- dfrac resource to ownership of [DfracDiscarded].

theorem own_dfrac_update (γ : GName) (dq : DFrac) :
    iOwn (E := e_dfrac) γ dq ⊢@{IProp GF} |==> iOwn (E := e_dfrac) γ DFrac.discard := by
  iapply iOwn_update
  apply DFrac.update_discard

-- Exercise: Use [own_dfrac_update] to prove the following Hoare triple.

set_option warn.sorry false in
theorem hoare_triple_dfrac (γ : GName) :
    {{ (iOwn (E := e_dfrac) γ (DFrac.own 1) : IProp GF) }}
      hl(#1 + #1)
    {{ v, RET v; iOwn (E := e_dfrac) γ DFrac.discard }} := by
  -- (exercise)
  sorry

end ghost
