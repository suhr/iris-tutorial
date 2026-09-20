import Iris.HeapLang
import Iris.Instances.Lib.Token

namespace Timeless
open Iris HeapLang

-- # Structured Concurrency

-- ## Introduction

-- As the reader might recall from the HeapLang chapter, the only
-- construct for concurrency supported natively by HeapLang is [Fork].
-- The [Fork] construction is an example of _unstructured_ concurrency.
-- When we use [Fork] to create a new thread, there are no control flow
-- constructs to reason about the termination of the forked thread – it
-- just runs until it is done and, upon completion, disappears.
--
-- When such control flow constructs are available, we call it
-- _structured_ concurrency. It turns out that we can implement
-- structured concurrency from unstructured concurrency, and we have
-- already seen two such examples: [spawn] and [par]. Both of these
-- constructs are part of HeapLang's library, but under the hood, they
-- are simply HeapLang programs defined in terms of the [Fork] primitive.
--
-- The library definitions additionally give and prove specifications for
-- the constructs, which we have used in previous chapters. In this
-- chapter, we will define the constructs from scratch and write our own
-- specifications for them.


-- ## The Fork Construct

-- Let us begin by revisiting the [Fork] construct. The operation takes
-- an expression [e] as an argument and spawns a new thread that executes
-- [e] concurrently. The operation itself returns the unit value on the
-- spawning thread.
--
-- [Fork] does not have dedicated tactical support. Instead, we simply
-- apply the lemma [wp_fork] – the specification for [Fork]. The lemma is
-- as follows.

#check wp_fork

-- For convenience, we include it here as well in `simplified' form.
--
--   [WP e {{_, True}} -∗ ▷ Φ #() -∗ WP Fork e {{v, Φ v}}]
--
-- That is, to show a weakest precondition of [Fork e], we have to show
-- the weakest precondition of [e] for a trivial postcondition. The key
-- point is that we only require the forked-off thread to be safe – we do
-- not care about its return value, hence the trivial postcondition.


-- ## The Spawn Construct

-- The first structured concurrency construct we study is [spawn]. This
-- consists of two functions: [spawn], which spawns a thread and returns
-- a `handle', and [join], which uses the handle to wait for a thread to
-- finish.
--
-- We define the functions as follows.

def spawn : Val := hl_val%
  λ f,
    let c := ref(none());
    fork(c ← some(f #()));
    c

def join : Val := hl_val%
  rec join c :=
    match !c with
    | none() => join c
    | some(x) => x

-- The idea with [spawn] is to create a `shared channel' which can be
-- used to signal when the forked-off thread has terminated. In this
-- case, the shared channel is simply a location containing an optional
-- value. When forking off the function ["f"], we wrap it around a store
-- operation, which writes the result of ["f"] into the location. The
-- location is then returned to the spawning thread, which can use this
-- so-called `handle' in the [join] function. The [join] function
-- continuously checks if the location has been updated to contain a
-- value. If this happens, the spawning thread knows that the forked-off
-- thread has finished, so it can extract the return value from the
-- location.
--
-- Considering this behaviour, we give [spawn] the specification:
--
-- [[
--   {{{ P }}} f #() {{{ v, RET v; Ψ v }}} -∗
--   {{{ P }}} spawn f {{{ h, RET h; join_handle h Ψ }}}
-- ]]
--
-- This states that to get a specification for [spawn f], we first must
-- prove a specification for [f] which captures which resources [f]
-- needs, [P], and what the value [f] terminates at satisfies, [Ψ]. If we
-- can prove such a specification for [f], then, given [P], we can also
-- run [spawn f], which will return a value [h] which satisfies a
-- `join-handle' predicate. This predicate is a promise that if we
-- invoke [join] with [h], then the value we get back satisfies [Ψ]. This
-- is reflected in the specification for [join]:
--
-- [[
--   {{{ join_handle h Ψ }}} join h {{{ v, RET v; Ψ v }}}.
-- ]]
--
-- Let us now prove these specifications.

section spawn

variable [HeapLangGS hlc GF]
def N := nroot .@ "handle"

-- Since we are using a shared channel, we will use an invariant to allow
-- the two (concurrently running) threads to access it. An initial
-- attempt at stating this invariant looks as follows.
def handle_inv1 (l : Loc) (Ψ : Val → IProp GF) : IProp GF := iprop%
  ∃ v : Val, l ↦ v ∗ (⌜v = hl_val(none())⌝ ∨ ∃ w : Val, ⌜v = hl_val(some(&w))⌝ ∗ Ψ w)

-- The stated invariant governs the shared channel (some location [l])
-- and states that either no value has been sent yet or some value has
-- been sent that satisfies the predicate [Ψ].
--
-- We can then use the invariant to define the [join_handle] predicate.
def join_handle1 (h : Val) (Ψ : Val → IProp GF) : IProp GF := iprop%
  ∃ l : Loc, ⌜h = hl_val(#l)⌝ ∗ inv N (handle_inv1 l Ψ)

-- Let us now attempt to prove the specification for [join].
set_option warn.sorry false in
theorem join_spec_1 (h : Val) (Ψ : Val → IProp GF) :
    {{ join_handle1 h Ψ }} hl(&join &h) {{ v, RET v; Ψ v }} := by
  unfold join_handle1
  iintro %Φ ⟨%l, %rfl, #I⟩ HΦ
  iloeb as IH
  wp_rec
  wp_bind !_
  iunfold handle_inv1 at I
  iinv I with ⟨%v, Hl, (>%rfl | ⟨%w, >%rfl, HΨ⟩)⟩
  · wp_load
    imodintro
    isplitl [Hl]
    · inext
      iexists hl_val(none())
      iframe
      ileft
      itrivial
    · wp_pures
      iapply IH
      iframe
  · wp_load
    imodintro
    -- Now we need [HΨ] to reestablish the invariant, but we also need it
    -- for the postcondition. We are stuck...
    sorry

-- We need a way to keep track of whether [Ψ w] has been `taken out' of
-- the invariant or not. However, we do not have any program state to
-- link it to. Instead, we will use _ghost state_ to track this
-- information. In particular, we will use _tokens_, which we introduced
-- in the Resource Algebra chapter. We here use the token implementation
-- from the Iris library, but it is similar to the version we
-- implemented.
variable [TokenG GF]

-- The trick is to have an additional state in the invariant which
-- represents the case where [Ψ w] has been taken out of the invariant.
-- This state simply mentions the token.

def handle_inv (γ : GName) (l : Loc) (Ψ : Val → IProp GF) : IProp GF := iprop%
  ∃ v, l ↦ some v ∗
    (⌜v = hl_val(none())⌝ ∨ (∃ w, ⌜v = hl_val(some(&w))⌝ ∗ Ψ w) ∨ token γ)

-- This enables the owner of the token to open the invariant, extract
-- [Ψ w], and close the invariant in the case that mentions the token. As
-- such, we include the token in the join handle so that [join] gets
-- access to the token.

def join_handle (h : Val) (Ψ : Val → IProp GF) : IProp GF := iprop%
  ∃ (γ : GName) (l : Loc), ⌜h = hl_val(#l)⌝ ∗ token γ ∗ inv N (handle_inv γ l Ψ)

-- Let us now try to prove the specifications again. We start with
-- [spawn].

theorem spawn_spec (P : IProp GF) (Ψ : Val → IProp GF) (f : Val) :
    {{ P }} hl(&f #()) {{ v, RET v; Ψ v }} -∗
    {{ P }} hl(&spawn &f) {{ h, RET h; join_handle h Ψ }} := by
  iintro #Hf %Φ !> HP HΦ
  wp_lam
  wp_alloc l with Hl
  wp_pures
  imod token_alloc with ⟨%γ, Hγ⟩
  imod inv_alloc N _ (handle_inv γ l Ψ) $$ [Hl] with #I
  · unfold handle_inv
    inext
    iexists hl_val(none())
    iframe
    ileft
    itrivial
  wp_apply wp_fork $$ [HΦ Hγ]
  · unfold join_handle
    wp_pures
    imodintro
    iapply HΦ
    iexists γ, l
    iframe Hγ #
    itrivial
  · unfold handle_inv
    wp_apply Hf $$ HP
    iintro %v HΨ
    wp_pures
    iinv I with ⟨%w, Hl, -⟩
    wp_bind _ ← _
    wp_store
    imodintro
    isplitl
    · imodintro
      iexists hl_val(injr(&v))
      iframe
      iright
      ileft
      iexists v
      iframe
      itrivial
    · itrivial

theorem join_spec (h : Val) (Ψ : Val → IProp GF) :
    {{ join_handle h Ψ }} hl(&join &h) {{ v, RET v; Ψ v }} := by
  unfold join_handle
  iintro %Φ ⟨%γ, %l, %rfl, Hγ, #I⟩ HΦ
  iloeb as IH
  wp_rec
  wp_bind ! #l
  -- We open the invariant and consider the three possible states.
  unfold handle_inv
  iinv I with ⟨%-, Hl, (>%rfl | ⟨%w, >%rfl, HΨ⟩ | >Hhγ')⟩
  · -- Case: The forked-off thread is not yet finished.
    wp_load
    imodintro
    isplitl [Hl]
    · inext
      iexists hl_val(none())
      iframe
      ileft
      itrivial
    · wp_pures
      iapply IH $$ Hγ
      iframe
  · -- Case: The forked-off thread has finished.
    wp_load
    imodintro
    -- Note that now, since we own the token, we do not need to use [Ψ w]
    -- to close the invariant – we close it with the token.
    isplitl [Hγ Hl]
    · inext
      iexists hl_val(injr(&w))
      iframe
    · wp_pures
      iapply HΦ $$ HΨ
  · -- Case: [Ψ w] has already been taken out of the invariant.
    -- This case is impossible as we own the token.
    icombine Hγ Hhγ' gives F
    iapply BI.false_elim $$ F

end spawn


-- ## The Par Construct

-- With [spawn] and [join] defined and their specifications proved, we
-- can move on to study a classical parallel composition operator: [par].
-- Its definition is quite straightforward – building on the [spawn]
-- construct.

def par : Val := hl_val%
  λ f1 f2,
    let h := &spawn f1;
    let v2 := f2 #();
    let v1 := &join h;
    (v1, v2)

-- We introduce familiar notation for [par] that hides the thunks.
local syntax:55 hl_exp:56 " ‖ " hl_exp:55 : hl_exp
local macro_rules
  | `(hl($e1 ‖ $e2)) => `(hl(&par (λ _, $e1) (λ _, $e2)))

-- Our desired specification for [par] is going to look as follows:
--
-- [[
--   {{{ P1 }}} e1 {{{ v, RET v; Ψ1 v }}} -∗
--   {{{ P2 }}} e2 {{{ v, RET v; Ψ2 v }}} -∗
--   {{{ P1 ∗ P2 }}} e1 ||| e2 {{{ v1 v2, RET (v1, v2); Ψ1 v1 ∗ Ψ2 v2 }}}
-- ]]
--
-- The rule states that we can run [e1] and [e2] in parallel if they have
-- _disjoint_ footprints and that we can verify the two components
-- separately. For this reason, the rule is sometimes also referred to as
-- the _disjoint concurrency rule_.  Note that this specification looks
-- slightly different from the specification in the [par] library:
-- [wp_par]. However, the differences are mainly notational.

section par

-- Since [par] is implemented with [spawn], we will use [spawn_spec] and
-- [par_spec] to prove the specification for [par]. As such, we will need
-- to include the resource algebra that those specifications rely on:
-- [token].

variable [HeapLangGS hlc GF] [TokenG GF]

-- It is actually quite straightforward to prove the [par] specification
-- as most of the heavy lifting is done by [spawn_spec] and [join_spec].
theorem par_spec (P1 P2 : IProp GF) (e1 e2 : Exp) (Q1 Q2 : Val → IProp GF) :
    {{ P1 }} e1 {{ v, RET v; Q1 v }} -∗
    {{ P2 }} e2 {{ v, RET v; Q2 v }} -∗
    {{ P1 ∗ P2 }} hl(&e1 ‖ &e2) {{ v1 v2, RET hl_val((&v1, &v2)); Q1 v1 ∗ Q2 v2 }} := by
  iintro #H1 #H2 %Φ !> ⟨HP1, HP2⟩ HΦ
  unfold par
  wp_pures
  -- We use [spawn_spec] to spawn a thread running [e1]. This requires us
  -- to prove that if [e1] terminates at value [v1], then [Q1 v1].
  -- However, this follows by our assumption ["H1"], so we easily prove
  -- this.
  wp_apply spawn_spec P1 Q1 $$ [] HP1
  · iintro %Φ1 !> HP1 HΦ1
    wp_pures
    iapply H1 $$ %Φ1 HP1
    iframe
  · -- We now get a join handle for the spawned thread, which guarantees us
    -- that the value we get upon joining with it satisfies [Q1].
    iintro %h Hh
    wp_pures
    -- Next, we execute [e2] in the current thread using its specification,
    -- ["H2"], which gives us that if [e2] terminates at some value [v2],
    -- then [Q2 v2].
    wp_apply H2 $$ HP2
    iintro %v2 HQ2
    wp_pures
    -- Finally, we join with the spawned thread using our join handle and
    -- [join_spec].
    wp_apply join_spec $$ Hh
    iintro %v1 HQ1
    wp_pures
    imodintro
    iapply HΦ
    iframe

end par

-- Let us try to use the [par] specification to prove a specification for a
-- simple client. The client performs two `fetch and add' operations on
-- the same location in parallel. The expression [FAA "l" #i] atomically
-- fetches the value at location [l], adds [i] to it, and stores the
-- result back in [l].
--
-- Our specification will state that the resulting value is even.

def parallel_add : Exp := hl%
  let r := ref(#0);
  faa(r, #2) ‖ faa(r, #6);
  !r

section parallel_add

-- We must again assume the presence of the [token] resource algebra as
-- we will be using the [par] specification, which relies on it through
-- [spawn].
variable [HeapLangGS hlc GF] [TokenG GF]

def N' := nroot .@ "par_add"

-- We will have an invariant stating that [r] points to an even integer.
def parallel_add_inv (r : Loc) : IProp GF := iprop%
  ∃ (n : Int), r ↦ hl_val(#n) ∗ ⌜2 ∣ n⌝

set_option warn.sorry false in
theorem parallel_add_spec :
    {{ (True : IProp GF) }}
      hl(&parallel_add)
    {{ (n : Int), RET hl_val(#n); ⌜2 ∣ n⌝ }} := by
  iintro %Φ - HΦ
  unfold parallel_add
  wp_alloc r with Hr
  wp_pure
  wp_pure
  imod inv_alloc N' _ (parallel_add_inv r) $$ [Hr] with #I
  · unfold parallel_add_inv
    inext
    iexists 0
    iframe
    ipureintro
    grind
  -- We don't need information back from the threads, so we will simply
  -- use [λ _, True] as the postconditions. Similarly, we only need the
  -- invariant to prove the threads, and since this is in the persistent
  -- context, we let the preconditions be [True].
  unfold parallel_add_inv
  wp_apply
    par_spec (GF := GF)
      iprop(True) iprop(True) hl(faa(#r, #2)) hl(faa(#r, #6))
      (fun _ => iprop(True)) (fun _ => iprop(True))
  · iintro %Φ' !> - HΦ'
    iinv I with ⟨%n, Hr, >%Hn⟩
    wp_faa
    imodintro
    isplitl [Hr]
    · iframe
      ipureintro
      grind
    · iapply HΦ'
      itrivial
  · iintro %Φ' !> - HΦ'
    iinv I with ⟨%n, Hr, >%Hn⟩
    wp_faa
    imodintro
    isplitl [Hr]
    · iframe
      ipureintro
      grind
    · iapply HΦ'
      itrivial
  · itrivial
  · -- (exercise)
    sorry

end parallel_add
