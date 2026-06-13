import Iris.HeapLang
-- import Iris.HeapLang.Lib.Spawn
import Iris.HeapLang.Lib.Par
import Iris.HeapLang.PrimitiveLaws
import Iris.HeapLang.ProofMode
import Iris.Algebra.DFrac

namespace Specifications
open Iris HeapLang Par

-- # Specifications
--
-- ## Introduction
--
-- Now that we have seen basic separation logic in Iris and introduced a
-- suitable language, HeapLang, we are finally ready to start reasoning
-- about programs. HeapLang ships with a program logic defined using
-- Iris. We can access the logic through the [proofmode] package, which
-- also defines tactics to alleviate working with the logic. The logic
-- provides constructs that allow us to specify the behaviour of HeapLang
-- programs. These specifications can then be proven by using rules
-- associated with the constructs. The tactics provided by the
-- [proofmode] package essentially just apply these rules.
--
-- The program logic for HeapLang relies on a basic notion of a resource
-- – the resource of heaps. Recall that [Σ] specifies the available
-- resources. To make the resource of heaps available, we have to specify
-- that [Σ] should contain it. The typeclass [heapGS] does exactly this.
-- Using [heapGS] and the [Context] command, we can assume that [Σ]
-- contains the resource of heaps throughout the [specifications]
-- section.

section specifications

variable [HeapLangGS hlc GF]

-- ## Weakest Precondition

-- The first construct for specifying program behaviour that we shall use
-- is the `weakest precondition'. To motivate it, let us consider a
-- simple example.

def arith : Exp := hl(#1 + #2 * #3 + #4 + #5)

-- This program should evaluate to [16]. We can express this in the logic
-- with a weakest precondition. In general, a weakest precondition has
-- the form [WP e {{v, Φ v}}]. This asserts that if the HeapLang program
-- [e] terminates at some value [v], then [v] satisfies the predicate
-- [Φ]. The double curly brackets [{{v, Φ v}}] is called the
-- `postcondition'. For the case of [arith], we would express its
-- behaviour using the following weakest precondition.

theorem arith_spec : ⊢@{IProp GF} WP arith {{ v, ⌜v = hl_val(#16)⌝}} := by
  unfold arith
  -- To prove this weakest precondition, we can use the tactics provided
  -- by [proofmode]. The initial step of the program is to multiply [#2]
  -- by [#3]. The tactic [wp_op] symbolically executes this expression
  -- using the underlying rules of the logic.
  wp_pure  -- PORTING: Iris-Lean does not support wp_op
  -- Note that the expression [#2 * #3] turned into [#(2 * 3)] – the Coq
  -- expression [2 * 3] is treated as a value in HeapLang.
  --
  -- In particular, [wp_op] has here applied three underlying rules:
  -- wp-bind, wp-op, and wp-val. The rule wp-bind allows us to `focus' on
  -- some sub-expression [e], which is the next part to be evaluated
  -- according to some evaluation context [K]. The rule is as follows:
  --
  --           [WP e {{ w, WP K[w] {{ v, Φ v }} }} ⊢ WP K[e] {{ v, Φ v }}]
  --
  -- This allows us to change the goal from
  --
  -- [WP (#1 + #2 * #3 + #4 + #5) {{ v, ⌜v = #16⌝ }}]
  --
  -- to
  --
  -- [WP #2 * #3 {{ w, WP (#1 + [] + #4 + #5)[w] {{ v, ⌜v = #16⌝ }} }}]
  --
  -- Next, the wp-op rule symbolically executes a single arithmetic
  -- operation, [⊚].
  -- [[
  --                           v = v₁ ⊚ v₂
  --             -------------------------------------------
  --             WP v {{ v, Φ v }} ⊢ WP v₁ ⊚ v₂ {{ v, Φ v }}
  -- ]]
  --
  -- We can thus perform the multiplication and change the goal to
  --
  -- [WP #(2 * 3) {{ w, WP (#1 + [] + #4 + #5)[w] {{ v, ⌜v = #16⌝ }} }}]
  --
  -- Finally, wp-val states that we can prove a weakest precondition of a
  -- value by proving the postcondition specialised to that value.
  --
  --                       [Φ(v) ⊢ WP v {{ w, Φ w }}]
  --
  -- The goal is changed to
  --
  -- [WP #1 + #(2 * 3) + #4 + #5 {{ v, ⌜v = #16⌝ }}]
  --
  -- This is where [wp_op] has taken us. The next step of the program is
  -- to add [#1] to [#(2 * 3)]. We could again use [wp_op] to
  -- symbolically execute this, but instead, we shall use the [wp_pure]
  -- tactic. This tactic can symbolically execute any pure expression.
  wp_pure
  -- Similarly to above, this tactic applies wp-bind, wp-op, and wp-val.
  --
  -- If there are several pure steps in a row, we can use the [wp_pures]
  -- tactic, which repeatedly applies [wp_pure].
  wp_pures
  -- When the expression in a weakest precondition turns into a value,
  -- the goal becomes proving the postcondition with said value
  -- (essentially applying wp-val). Technically, the goal is to prove the
  -- postcondition behind a `fancy update modality'. This functionality
  -- is related to resources and invariants, so we skip it for now. We
  -- can always remove a fancy update modality in the goal with
  -- [iModIntro].
  imodintro
  ipureintro
  rfl

-- Let us look at another example of a pure program. The `lambda' program
-- from lang.v consists of only let expressions, lambdas, applications,
-- and arithmetic.

def lambda : Exp := hl%
  let add5 := (λ x, x + #5);
  let double := (λ x, x * #2);
  let compose := (λ f g, (λ x, g (f x)));
  (compose add5 double) #5

-- The program logic for HeapLang provides specific tactics to
-- symbolically execute these kinds of expressions, e.g. [wp_let] for let
-- expressions, [wp_lam] for applications, and [wp_op] for arithmetic. A
-- list of all tactics for HeapLang expressions can be found at
--
-- <<https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/heap_lang.md#tactics>>
--
-- These tactics similarly apply the underlying rules of the logic,
-- however, we shall from now on refrain from explicitly mentioning the
-- rules applied. Through experience, the reader should get an intuition
-- for how each tactic manipulates the goal.
--
-- Exercise: prove the following specification for the lambda program.

theorem lambda_spec : ⊢@{IProp GF} WP lambda {{ v, ⌜v = hl_val(#20)⌝ }} := by
  unfold lambda
  wp_pures
  imodintro
  ipureintro
  rfl

-- ## Resources
--
-- In this section, we introduce our first notion of a resource: the
-- resource of heaps. As mentioned in basics.v, propositions in Iris
-- describe/assert ownership of resources. To describe resources in the
-- resource of heaps, we use the `points-to' predicate, written [l ↦ v].
-- Intuitively, this describes all heap fragments that have value [v]
-- stored at location [l]. The proposition [l1 ↦ #1 ∗ l2 ↦ #2] then
-- describes all heap fragments that map [l1] to [#1] and [l2] to [#2].
--
-- To see this in action, let us consider a simple program.
def prog : Exp := hl%
  -- Allocate the number [1] on the heap -/
  let x := ref(#1);
  -- Increment [x] by [2] -/
  x ← !x + #2;
  -- Read the value of [x] -/
  !x

-- This program should evaluate to [3]. We express this with a weakest
-- precondition.
theorem prog_spec : ⊢@{IProp GF} WP prog {{ v, ⌜v = hl_val(#3)⌝ }} := by
  unfold prog
  -- The initial step of [prog] is to allocate a reference containing the
  -- value [1]. We can symbolically execute this step of [prog] using the
  -- [wp_alloc] tactic. As a result of the allocation, we get the
  -- existence of some location [l] which points-to [1], [l ↦ #1]. The
  -- [wp_alloc] tactic requires that we give names to the location and the
  -- proposition.
  wp_bind ref(_)
  iapply wp_alloc
  iintro !> %l Hl
  -- The next step of [prog] is a let expression which we symbolically
  -- execute with [wp_let].
  wp_pures
  -- Next, we load from location [l]. Loading from a location requires
  -- the associated points-to predicate in the context. The predicate
  -- then governs the result of the load. Since we have [Hl], we can
  -- perform the load using the [wp_load] tactic.
  wp_bind !#l
  iapply wp_load $$ [$]
  iintro !> Hl
  -- Then we evaluate the addition.
  wp_pures
  -- Storing is handled by [wp_store]. As with loading, we must have the
  -- associated points-to predicate in the context. [wp_store] updates
  -- the points-to predicate to reflect the store.
  wp_bind #l ← _
  iapply wp_store $$ [$]
  iintro !> Hl
  wp_pures
  -- Finally, we use [wp_load] again.
  iapply wp_load $$ [$]
  iintro !> Hl
  -- Now we are left with a trivial proof that [1 + 2 = 3]
  ipureintro
  rfl

-- HeapLang also provides the [CmpXchg] instruction to interact with the
-- heap. The [wp_cmpxchg] symbolically executes an instruction on the
-- form [CmpXchg l v1 v2]. As with [wp_load] and [wp_store], [wp_cmpxchg]
-- requires the associated points-to predicate [l ↦ v]. If this is
-- present in the context, then [wp_cmpxchg as H1 | H2] will generate two
-- subgoals. The first corresponds to the case where the [CmpXchg]
-- instruction succeeded. Thus, we get to assume [H1 : v = v1], and our
-- points-to predicate for [l] is updated to [l ↦ v2]. The second
-- corresponds to the case where [CmpXchg] failed. We instead get
-- [H2 : v ≠ v1], and our points-to predicate for [l] is unchanged.
--
-- Let us demonstrate this with a simple example program which simply
-- checks if a given location contains the number 0 and, if it does,
-- updates it to 10.

def cmpXchg_0_to_10 (l : Loc) : Exp := hl(cmpXchg(#l, #0, #10))

-- PORTING: Iris-lean does not support `wp_cmpxchg` yet
-- theorem cmpXchg_0_to_10_spec (l : Loc) (v : Val) :
--   l ↦ v -∗
--   WP (cmpXchg_0_to_10 l) {{ u, (⌜v = hl_val(#0)⌝ ∗ l ↦ hl_val(#10)) ∨
--                                (⌜v ≠ hl_val(#0)⌝ ∗ l ↦ v) }} := by
--   iIntros "Hl".
--   wp_cmpxchg as H1 | H2.
--   -- CmpXchg succeeded
--     iLeft.
--     by iFrame.
--   -- CmpXchg failed
--     iRight.
--     by iFrame.
--  sorry

-- If it is clear that a [CmpXchg] instruction will succeed, then we can
-- apply the [wp_cmpxchg_suc] tactic which will immediately discharge the
-- case where [CmpXchg] fails. Similarly, we can use [wp_cmpxchg_fail]
-- when a [CmpXchg] instruction will clearly fail.
--
-- Recall the [cas] example from lang.v

def cas : Exp := hl%
  let l := ref(#5);
  if cas(l, #6, #7) then
    #()
  else
    let a := !l;
    if cas(l, #5, #7) then
      let b := !l;
      (a, b)
    else
      #()

-- The result of both [CAS] instructions is predetermined. Hence, we can
-- use the [wp_cmpxchg_suc] and [wp_cmpxchg_fail] tactics to symbolically
-- execute them (remember that [CAS l v1 v2] is syntactic sugar for
-- [Snd (CmpXchg l v1 v2)]).
-- Exercise: finish the proof of the specification for [cas].

-- theorem cas_spec : ⊢@{IProp GF} WP cas {{ v, ⌜v = hl_val((#5, #7)) ⌝ }} := by
--   rewrite /cas.
--   wp_alloc l as "Hl".
--   wp_let.
--   wp_cmpxchg_fail.
--   wp_proj.
--   wp_if.
--   -- exercise
--   sorry

-- We finish this section with a final remark about the points-to
-- predicate. One of its essential properties is that it is not
-- duplicable. That is, for every location [l], there can only exist one
-- points-to predicate associated with it [l ↦ v]. This is captured by
-- the following theorem.
theorem pt_not_dupl (l : Loc) (v v' : Val) : l ↦ v ∗ l ↦ v' ⊢ False := by
  unfold pointsTo
  iintro ⟨h1, h2⟩
  icombine h1 h2 gives ⟨%h, %_⟩
  ipureintro
  simp [DFrac.op_own, DFrac.valid_iff, Rat.add_def] at h
  exact absurd h (by decide)

-- PORTING: TODO: Composing Programs and Proofs, Hoare Triples, Concurrency

end specifications
