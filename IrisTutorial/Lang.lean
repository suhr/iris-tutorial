import Iris.HeapLang
import Iris.HeapLang.Lib.Spawn
import Iris.HeapLang.Lib.Par

namespace Lang
open Iris HeapLang Spawn Par

-- # HeapLang

-- ## Introduction

-- HeapLang is an untyped concurrent programming language with a heap. It
-- is an ML-like language, sporting many of the usual constructs such as
-- let expressions, lambda abstractions, and recursive functions. It also
-- supports higher-order functions. The evaluation order is right to left
-- and it is a call-by-value language.
--
-- The syntax for HeapLang is fairly standard, but there are some quirks
-- as we are working inside Coq. As the features of HeapLang are fairly
-- standard, the focus in this chapter is mainly on showcasing the syntax
-- of the language through simple defs.

-- ## The HeapLang Interpreter (Optional)

-- HeapLang is primarily made to be reasoned about using Iris. However,
-- there is a rudimentary interpreter for HeapLang located in
-- [iris.unstable.heap_lang]. The interpreter provides the function
-- [exec], which takes as input some fuel and an expression. The
-- expression is then executed until it terminates at a value [v], the
-- execution runs out of fuel, or the program gets stuck. In case of
-- termination, [inl v] is returned. Otherwise [inr err] is returned,
-- with [err] describing the error.
--
-- By default, the interpreter is not installed as it can only be used
-- with development versions of Iris. The interpreter is not required for
-- the tutorial, but it can optionally be installed for this chapter. To
-- install it, run:
--
--   <<opam install coq-iris-unstable>>
--
-- This also updates Iris to a development version. To access the
-- interpreter, uncomment the import below.

-- From iris.unstable.heap_lang Require Import interpreter.

-- To return to a release version of Iris known to be compatible with the
-- rest of the tutorial, run:
--
--   <<opam install . --deps-only>>
--
-- This also uninstalls the interpreter.

-- ## Pure Constructs

section heaplang

-- HeapLang has native support for integers and booleans. With these, we
-- can do basic arithmetic and control flow.
-- Note that values in HeapLang are prefixed by a [#].
def arith : Exp := hl% #1 + #2 * #3

-- If the interpreter was installed, the expression can now be executed
-- using [(exec 10 arith)], where [10] is the amount of fuel. To evaluate
-- the execution inside Coq, we can use the [Compute] command. Uncomment
-- the command below to see this in action.

-- Compute (exec 10 arith).
-- * Evaluates to [inl #7]

def booleans : Exp := hl% (&arith = #7) && #true || (#true = #false)

-- Compute (exec 10 booleans).
-- * Evaluates to [inl #true]

def if_then_else : Exp := hl% if &booleans then #() else #false

-- Compute (exec 10 if_then_else).
-- * Evaluates to [inl #()]

-- Heaplang supports let expressions. Technically, let expressions are
-- not native to HeapLang. We get let expressions from the [notation]
-- package, which defines them in terms of lambda abstractions.
-- Note that variables in HeapLang are strings.

def lets : Exp := hl%
  let a := #4;
  let b := #2;
  a + b

-- Compute (exec 10 lets).
-- * Evaluates to [inl #6]

-- HeapLang has native support for pairs, with tuples being notation for
-- nested pairs.

def pairs : Exp := hl%
  let p := (#40, #1 + #1);
  fst(p) + snd(p)

-- Compute (exec 10 pairs).
-- * Evaluates to [inl #42]

def tuples : Exp := hl%
  let t1 := (#1, #2, #3, #4);
  let t2 := (((#1, #2), #3), #4);
  snd(fst(fst(t1))) = snd(fst(fst(t2)))

-- Compute (exec 10 tuples).
-- * Evaluates to [inl #true]

-- We can also do pattern matching using sums. A common use case of sums
-- is the `option' construction. The [notation] package has us covered
-- here as well.

def sums : Exp := hl%
  let r := injr(#1);
  match r with
  | injl(n) => #0
  | injr(n) => n + #1

-- Compute (exec 10 sums).
-- * Evaluates to [inl #2]

def option : Exp := hl%
  let r := some(#1);
  match r with
  | none() => #0
  | some(n) => n + #1

-- Compute (exec 10 option).
-- * Evaluates to [inl #2]

-- Finally, we have lambda abstractions and recursive functions. As with
-- let expressions, lambda abstractions are also a derived construct –
-- they are recursive functions that do not recurse. In HeapLang,
-- functions are first-class citizens, which gives support for
-- higher-order functions.

def lambda : Exp := hl%
  let add5 := (λ x, x + #5);
  let double := (λ x, x * #2);
  let compose := (λ f g, (λ x, g (f x)));
  (compose add5 double) #5

-- Compute (exec 10 lambda).
-- * Evaluates to [inl #20]

def recursion : Exp := hl%
  let fac :=
    (rec f n := if n = #0 then #1 else n * f (n - #1));
  (fac #4, fac #5)

-- Compute (exec 25 recursion).
-- * Evaluates to [inl (#24, #120)]

-- ## References

-- References are dynamically allocated through the [ref] instruction.
-- Given a value, [ref] finds a fresh location on the heap and stores the
-- value there. The location is then returned.

def alloc : Exp := hl%
  let l1 := ref(#0);
  let l2 := ref(#0);
  (l1, l2)

-- Compute (exec 10 alloc).
-- * Evaluates to [inl (#(Loc 1), #(Loc 2))]

-- After allocation, we can read and update the value at the returned
-- location [l] with [!l] and [l <- v], respectively.

def load : Exp := hl%
  let l := ref(#5);
  !l

-- Compute (exec 10 load).
-- * Evaluates to [inl #5]

def store : Exp := hl%
  let l := ref(#5);
  l ← #6 ;
  !l

-- Compute (exec 10 store).
-- * Evaluates to [inl #6]

-- To allow for synchronisation between threads, HeapLang provides a
-- single primitive called compare-and-exchange, written
-- [CmpXchg l v1 v2]. This instruction atomically reads the contents of
-- location [l], checks if it is equal to [v1], and, in case of equality,
-- updates [l] to contain [v2]. The instruction returns a pair [(v, b)],
-- with [v] being the original value stored at [l], and [b] a boolean
-- indicating whether the location was updated.

def cmpxchg_fail : Exp := hl%
  let l := ref(#5);
  cmpXchg(l, #6, #7)

-- Compute (exec 10 cmpxchg_fail).
-- * Evaluates to [inl (#5, #false)]

def cmpxchg_suc : Exp := hl%
  let l := ref(#5);
  cmpXchg(l, #5, #7)

-- Compute (exec 10 cmpxchg_suc).
-- * Evaluates to [inl (#5, #true)]

-- The [notation] package defines a variant of [CmpXchg] called
-- compare-and-set, written [CAS l v1 v2]. The only difference is that
-- [CAS] only returns the boolean [b].

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

-- Compute (exec 10 cas).
-- * Evaluates to [inl (#5, #7)]

-- ## Concurrency

-- HeapLang has only one primitive for concurrency: [Fork]. The
-- instruction [Fork e] creates a new thread which executes [e]. The
-- invoking thread continues execution after creation. If the computation
-- of [e] terminates, then the resulting value is simply thrown away.
-- Hence, [e] is only run for its side effects.

def fork : Exp := hl%
  let l := ref(#5);
  fork(l ← #7);
  !l

-- Unfortunately, in its current state, the HeapLang interpreter does not
-- support concurrency; the forked thread never executes its expression.
-- Hence, the above program will always return [5]. Of course, this is
-- only a limitation of this specific interpreter – HeapLang is still a
-- concurrent programming language, and we still have to reason about
-- forked threads inside the Iris logic.

-- Compute (exec 10 fork).
-- * Evaluates to [inl #5]

-- From the [Fork] primitive, we can implement several other
-- constructions for concurrency. HeapLang ships with two such
-- constructions, [spawn] and [par], which we will implement and prove
-- correct later.

-- [spawn] takes a thunked expression and creates a new thread which
-- executes said expression. Additionally, [spawn] returns a handle,
-- which we can use in conjunction with [join] to wait for the result of
-- the computation.

example : Exp := hl%
  let l := ref(#5);
  let handle := &spawn (λ _, l ← #6; #2);
  let res := &join handle;
  let v := !l;
  (res, v)

-- * Evaluates to [(2, 6)].

-- Using the [spawn] construct, we can define [par] which runs two
-- expressions in parallel. We define the notation [e1 ||| e2] for
-- [par], which states that [e1] and [e2] are run in parallel. Once both
-- expressions have terminated, the resulting values are returned in a
-- pair.

def par : Exp := hl%
  let l := ref(#5);
  let res := (!l + #1) ‖ (!l + #2);
  fst(res) + snd(res)

-- * Evaluates to [13].

end heaplang
