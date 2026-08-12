import Iris.HeapLang
import Iris.HeapLang.Lib.Par

namespace Later
open Iris HeapLang Par

-- # Invariants

-- ## Motivating Example

-- Let us make a simple multi-threaded program.

def prog : Exp := hl%
  let l := ref(#0);
  fork(l ← #1);
  !l

-- This program will race to either update [l] or read [l], meaning the
-- resulting value could be either [0] or [1].

section proofs
variable [HeapLangGS hlc GF]

-- theorem wp_prog :
--     {{ (True : IProp GF) }} prog {{ v, RET v; ⌜v = hl_val(#0)⌝ ∨ ⌜v = hl_val(#1)⌝ }} := by
--   iintro %Φ _ HΦ
--   unfold prog
--   wp_alloc l with Hl
--   wp_pures
--   -- Fork does not have its own tactic. Instead, we use its
--   -- specification. This specification forces us to split our resources
--   -- between the threads.
--   wp_bind fork(_)
--   iapply wp_fork $$ [Hl]
--   -- As such, we must pick a thread to own [l]. But as both threads need
--   -- to access [l], we are stuck.
--   · sorry
--   · sorry

-- ## Introduction to Invariants

section inv_intro

-- As the above program illustrates, some resources are required by
-- multiple threads simultaneously. If those resources are not shareable
-- (i.e. persistent), then we will get stuck, as in the example above. To
-- get around this problem, we can devise an invariant for said
-- resources. That is, we come up with a proposition [P] which describes
-- the resources in a way that is always true, no matter where in the
-- program we are or how threads have interleaved. We can then use Iris'
-- invariant functionality to assert that [P] is an invariant: [inv N P].
-- Here, [N] is a `namespace', which we may think of as the name of the
-- invariant.
--
-- The key property of invariants that solve our problem is that they are persistent.

theorem inv_persist (N : Namespace) (P : IProp GF) : BI.Persistent (inv N P) :=
  by infer_instance

-- Thus, if we can come up with a proposition [P] describing our
-- resources correctly throughout the entire program, then we can
-- _allocate_ [P] as an invariant, and supply said invariant to the
-- threads requiring access to the resources described by [P]. To access
-- [P] from the invariant, threads must then _open_ the invariant.
--
-- The next two sub-sections cover how to open and allocate invariants.

-- ### Opening Invariants

-- Once we have an invariant [inv N P], we can use the [iInv] tactic to
-- _open_ the invariant, granting us access to [P]. To ensure soundness
-- of the logic, there are some restrictions to opening an invariant.
--
-- Firstly, an invariant can only be opened once before being closed
-- again. This is enforced in Iris through `masks'. A mask can be thought
-- of as a set that tracks which invariants are closed. If no invariants
-- are open, the mask is [⊤]. If only invariant [N] is open, the mask is
-- [⊤ ∖ ↑N]. If we have two invariants [N1] and [N2] that are both open,
-- the mask is [⊤ ∖ ↑N1 ∖ ↑N2], and so on. Only invariants that are in
-- the mask can be opened. Thus, if invariant [N] is not in the mask
-- (i.e. it is open), then we cannot use [iInv] to open [N] again.
-- Closing the invariant puts [N] back into the mask, allowing it to be
-- opened again. Closing an open invariant [iInv N P] corresponds to
-- proving that [P] still holds.
--
-- We can only open an invariant if the goal has a mask which contains
-- [N]. As such, if the goal is a generic proposition, we cannot open any
-- invariants.

-- theorem inv_open_fail (N : Namespace) (P Q : IProp GF) : inv N P ⊢ Q := by
--   iintro Hinv
--   fail_if_success iinv Hinv with HP
--   sorry

-- An example of a goal that has a mask is a weakest precondition. That
-- is, the shape of a weakest precondition is actually
--
--   [WP e @ E {{ Φ }}]
--
-- with [E] being the mask. However, when the mask is [⊤], it is
-- notationally hidden, which is why we have yet to see it.
--
-- Another example of a goal permitting invariant openings is the _fancy
-- update modality_, which essentially just adds a mask to the update
-- modality. A fancy update modality is written [|={E}=>] for a mask [E].
-- The fancy update modality is like the update modality but with support
-- for invariants: if the goal contains [|={E}=>], then we are allowed to
-- open all invariants in [E].

-- Another restriction on invariant openings is that when the goal is a
-- weakest precondition [WP e {{Φ}}], an invariant can be open for at
-- most one program step. This is enforced by requiring [e] to be an
-- atomic expression, meaning it reduces to a value in one step. After
-- the one step, we have to close the invariant again.
--
-- Let us try to see these concepts in action with a simple example.

-- theorem inv_open_example_attempt_1 (N : Namespace) (l : Loc) :
--     inv N (l ↦ hl_val(#1)) ⊢ WP hl(!#l + !#l) {{ v, ⌜v = hl_val(#2)⌝ }} := by
--   iintro #Hinv
--   -- To prove the WP, we must get access to [l ↦ #1] from the invariant.
--   -- As discussed, to open the invariant, the expression must be atomic.
--   -- Let us ignore this and try to open the invariant anyway.
--   iinv Hinv with Hl
--   -- Iris now asks us to prove that [!#l + !#l] is atomic. Hence we are
--   -- stuck.
--   · sorry
--   · sorry

-- theorem inv_open_example_attempt_2 (N : Namespace) (l : Loc) :
--     inv N (l ↦ hl_val(#1)) ⊢ WP hl(!#l + !#l) {{ v, ⌜v = hl_val(#2)⌝ }} := by
--   iintro #Hinv
--   -- We now first bind the expression ([!#l]), which _is_ atomic.
--   wp_bind !#l
--   iinv Hinv with Hl
--   · show (nclose N) ⊆ ⊤ ∧ ProgramLogic.Language.Atomic ↑Stuckness.NotStuck hl(!#l)
--     simp
--     exact instAtomicLoad
--   -- This tactic did quite a bit, so let us break it down.

--   -- Firstly, notice that we got the points-to predicate from the
--   -- invariant. A small caveat is that we only get the predicate later.
--   -- This is usually not an issue, as the later can be removed in most
--   -- cases, which we discuss in a later chapter.

--   -- Secondly, the postcondition of the weakest precondition in the goal
--   -- was augmented with [|={⊤ ∖ ↑N}=> ▷ l ↦ #1]. After stepping through
--   -- the current WP, we will have to prove this proposition to show that
--   -- the invariant [l ↦ #1] still holds. The fancy update modality is
--   -- there to stop us from opening the invariant to prove that the
--   -- invariant still holds.

--   -- Thirdly, notice the mask on the weakest precondition: [⊤ ∖ ↑N]. This ensures
--   -- that we cannot open [N] again to prove the WP. If we tried to open
--   -- the invariant again, Iris would ask us to show that [↑N] is a subset
--   -- of [⊤ ∖ ↑N]. For the sake of demonstration, let us try this.
--   iinv Hinv with Hl'
--   -- This is of course impossible to prove, so we are stuck.
--   · sorry
--   · sorry

theorem inv_open_example (N : Namespace) (l : Loc) :
    inv N (l ↦ hl_val(#1)) ⊢ WP hl(!#l + !#l) {{ v, ⌜v = hl_val(#2)⌝ }} := by
  iintro #Hinv
  -- We now first bind the expression ([!#l]), which _is_ atomic.
  wp_bind !#l
  iinv Hinv with Hl
  -- Having opened the invariant, we now have access to [l ↦ #1], which
  -- we can use to prove the WP.
  wp_load
  -- Now that we have used our invariant to take the one step, we must
  -- close the invariant by proving that the invariant still holds.
  isplitl [Hl]
  · iexact Hl
  -- Even though we have now closed the invariant, the fancy
  -- update modality still prevents us from opening the invariant.
  -- However, we can always introduce a fancy update modality with
  -- [iModIntro].
  imodintro
  -- Since the mask on the weakest precondition in the goal is implicitly
  -- [⊤], we can open [N] again.

  -- We have now used the invariant to reduce the right-hand [!#l].
  -- Reducing the left-hand dereference is done analogously.
  -- First, we bind the dereference.
  wp_bind !#l
  -- Then we open the invariant.
  iinv Hinv with Hl
  -- Next, we use the contents of the invariant to prove the dereference.
  wp_load
  -- Finally, we close the invariant by proving it still holds.
  isplitl [Hl]
  · iexact Hl
  -- Now, both dereferences have been reduced, so we easily prove the
  -- remaining WP.
  imodintro
  wp_pure
  itrivial

-- ### Allocating Invariants

-- Now we know how to open invariants, but how are they created in the
-- first place?
--
-- Once we have devised a proposition [P] describing our resources
-- invariantly, we can turn [P] into an invariant [inv N P] using the
-- [inv_alloc] lemma. The lemma states
--
--     [inv_alloc : ▷P -∗ |={E}=> inv N P]
--
-- That is, to turn [P] into an invariant, we must prove that [P] is true
-- after one step (or, if we can, in the current step). As with
-- allocation of ownership of resources, we do not get access to the
-- invariant immediately; it is behind a fancy update modality
-- [|={E}=>].
--
-- Let us see this in action. First, we give a name to the invariant we
-- wish to allocate.

def N := nroot .@ "myNamespace"

-- Now, let us try to prove the following (quite contrived)
-- specification.

theorem inv_alloc_loc :
    {{ True }} hl(ref(#0)) {{(l : Loc), RET hl_val(#l); inv N (l ↦ hl_val(#0))}} := by
  iintro %Φ _ HΦ
  wp_alloc l with Hl
  -- We now wish to allocate the invariant using [inv_alloc]. To strip
  -- the fancy update modality immediately, we use the [iMod] tactic.
  -- We can do this since the goal contains a fancy update modality.
  imod inv_alloc N _ (l ↦ hl_val(#0)) $$ [Hl] with Hinv
  -- As discussed, in order to allocate the invariant, we must prove that
  -- it holds after one step.
  · inext
    itrivial
  -- With the invariant allocated, we can finish the proof.
  imodintro
  iapply HΦ $$ Hinv

-- Side note: The above proof demonstrates why, when we have to prove the
-- postcondition of a WP, we have to prove it _behind_ a fancy update
-- modality. Having the fancy update modality in the goal allows us to
-- allocate/open invariants and allocate/update resources.

end inv_intro

-- ## A Motivating Example – Take Two

-- Armed with the knowledge of invariants, let us attempt to prove the
-- specification from the beginning of the chapter again. We start by
-- giving a name to our invariant.
def N₁ := nroot .@ "prog"

-- So what should the invariant be? The resource of interest is what the
-- location [l] points to, and throughout the program, it points to
-- either [0] or [1]. As such, we will create an invariant which captures
-- that [l] points to either [0] or [1].
@[reducible] def prog_inv (l : Loc) : IProp GF := iprop%
  ∃ v, l ↦ some v ∗ (⌜v = hl_val(#0)⌝ ∨ ⌜v = hl_val(#1)⌝)

theorem wp_prog :
    {{ (True : IProp GF) }} prog {{ v, RET v; ⌜v = hl_val(#0)⌝ ∨ ⌜v = hl_val(#1)⌝ }} := by
  iintro %Φ _ HΦ
  unfold prog
  wp_alloc l with Hl
  wp_pures
  -- We now allocate our [prog_inv] invariant using [inv_alloc].
  imod inv_alloc N₁ _ (prog_inv l) $$ [Hl] with #Hinv
  -- We prove that the invariant is currently true.
  · inext
    iexists hl_val(#0)
    iframe
    ileft
    itrivial
  -- With the invariant allocated and in the persistent context, we can
  -- use it to prove both threads.
  wp_bind fork(_)
  iapply wp_fork $$ [HΦ]
  · inext
    wp_pures
    iinv Hinv with ⟨%v, >Hl, >#Hi⟩
    wp_load
    isplitr [HΦ]
    · iexists v
      iframe
      itrivial
    · iapply HΦ $$ Hi
  · inext
    -- As [#l <- #1] is atomic and the mask on the WP is [⊤], we can open the invariant.
    iinv Hinv with ⟨%v, >Hl, >#Hi⟩
    -- We use the obtained points-to predicate to prove the WP.
    wp_store
    -- We close the invariant...
    isplitl
    · iexists hl_val(#1)
      iframe
      itrivial
    -- ... and finish the proof of the forked thread.
    itrivial

end proofs

-- ## Another Example

-- Let us look at another program. This program will create a thread to
-- continuously increment a counter while the main thread will read the
-- counter at some point. As such, this program should produce some
-- non-negative number. However, we will only prove that it returns a
-- number. Later, we will see other tools that will allow us to refine
-- this.

def prog2 : Exp := hl%
  let l := ref(#0);
  fork((
    rec go _ :=
      l ← !l + #1;
      go #()
  ) #());
  !l

section proofs
variable [HeapLangGS hlc GF]

def N₂ := nroot .@ "prog2"

-- Our invariant will simply be that the location points to an integer.
@[reducible] def prog2_inv (l : Loc) : IProp GF := iprop%
  ∃i : Int, l ↦ hl_val(#i)

theorem prog2_spec :
    {{ (True : IProp GF) }} prog2 {{ (i : Int), RET hl_val(#i); True }} := by
  iintro %Φ _ HΦ
  unfold prog2
  wp_alloc l with Hl
  wp_pures
  -- Like before, we allocate the invariant.
  imod inv_alloc N₁ _ (prog2_inv l) $$ [Hl] with #I
  · iexists 0;  iframe
  wp_bind fork(_)
  iapply wp_fork $$ [HΦ]
  · inext
    wp_pures
    iinv I with ⟨%i, >Hl⟩
    wp_load
    imodintro
    isplitl [Hl]
    · iexists i; iframe
    iapply HΦ
    itrivial
  · inext
    wp_pure
    -- We use löb induction to accent the recursive calls.
    iloeb as ih
    wp_pures
    -- We need to access the contents of the invariant to step through
    -- the read of [l] and the store to [l]. However, invariants can only
    -- be open for one step, so we are forced to open the invariant twice
    -- in succession.
    -- First, we open it around the read.
    wp_bind !_
    iinv I with ⟨%i, >Hl⟩
    wp_load
    imodintro
    isplitl [Hl]
    · iexists i; iframe
    wp_pures
    -- Next, we open it around the store.
    wp_bind _ ← _
    iinv I with ⟨%_, >Hl⟩
    wp_store
    imodintro
    isplitl [Hl]
    · iexists i + 1; iframe
    wp_pure;  wp_pure
    iapply ih
    itrivial

end proofs
