import Iris.HeapLang
import Iris.BI.BigOp.BigSepList

namespace LinkedLists
open Iris HeapLang

-- # Case Study: Linked Lists

section linked_lists
variable [HeapLangGS hlc GF]

-- In this chapter, we will study several functions on linked lists. To
-- do this, we must first agree on what a linked list is. In HeapLang, we
-- can implement linked lists as chains of pointers. We define this
-- formally with a predicate, which we denote [isList]. This predicate
-- turns a list of values [xs] into a predicate describing the structure
-- of the linked list.

def isList (l : Val) (xs : List Val) : IProp GF :=
  match xs with
  | [] => iprop(⌜l = hl_val(none())⌝)
  | x :: xs => iprop%
    ∃ (hd : Loc) (l' : Val), ⌜l = hl_val(some(#hd))⌝ ∗ hd ↦ hl_val((&x, &l')) ∗ isList l' xs

-- We can now define HeapLang functions that act on lists, such as [inc].
-- The [inc] function recursively increments all the values of a list.

def inc : Val := hl_val%
  rec inc l :=
    match l with
    | none() => #()
    | some(hd) =>
      let x := fst(!hd);
      let l' := snd(!hd);
      hd ← (x + #1, l');
      inc l'

-- Intuitively, the specification we give for this function should state
-- that the linked list should only contain integers and that, after
-- executing the function, each integer has been incremented. As such, we
-- parametrise the specification not by a list of values, but by a list
-- of integers. We then map each integer to a HeapLang value using [# _],
-- allowing us to use the [isList] predicate.
theorem inc_spec (l : Val) (xs : List Int) :
    {{ (isList l ((fun x : Int => hl_val(#x)) <$> xs) : IProp GF) }}
      hl(&inc &l)
    {{ RET hl_val(#()); isList l ((fun x => hl_val(#(x + 1 : Int))) <$> xs) }} := by
  -- The proof proceeds by structural induction in [xs]. As [l] changes in each
  -- iteration, we must universally quantify over it to strengthen the induction
  -- hypothesis.
  induction xs generalizing l with
  | nil =>
    -- PORTING: iris-lean does not support iintro with [→] and [←]
    iintro %Φ Hil HΦ
    isimp [Functor.map, List.map_nil, isList] at Hil HΦ
    icases Hil with %Hil
    wp_rec
    isimp [Hil]
    wp_match
    imodintro
    iapply HΦ $$ %Hil
  | cons x xs ih =>
    iintro %Φ Hil HΦ
    isimp [Functor.map, List.map_cons, isList] at Hil HΦ
    icases Hil with ⟨%hd, %l', %hl, hhd, hxs⟩
    wp_rec
    isimp [hl]
    wp_load
    wp_load
    wp_store
    wp_pures
    iapply ih l' $$ %Φ hxs
    iintro !> Hl
    iapply HΦ
    iexists _, _
    iframe ∗ %hl

-- The append function recursively descends [l1], updating the links.
-- Eventually, it reaches the tail, [NONE], where it will replace it with
-- [l2].
def append : Val := hl_val%
  rec append l1 l2 :=
    match l1 with
    | none() => l2
    | some(hd) =>
      let x := fst(!hd);
      let l1' := snd(!hd);
      let r := append l1' l2;
      hd ← (x, r);
      some(hd)

-- If [l1] and [l2] represent the lists [xs] and [ys] respectively, then
-- we expect that [append l1 l2] will return a list representing
-- [xs ++ ys].
theorem append_spec (l1 l2 : Val) (xs ys : List Val) :
    {{ (isList l1 xs : IProp GF) ∗ isList l2 ys }}
      hl(&append &l1 &l2)
    {{ l, RET l; isList l (xs ++ ys) }} := by
  induction xs generalizing l1 l2 ys with
  | nil =>
    iintro %Φ ⟨Hi1, Hi2⟩ HΦ
    isimp [isList] at Hi1
    isimp at HΦ
    icases Hi1 with %Hi1
    unfold append
    isimp [Hi1]
    wp_pures
    imodintro
    iapply HΦ $$ Hi2
  | cons x xs ih =>
    iintro %Φ ⟨Hi1, Hi2⟩ HΦ
    isimp [isList] at Hi1 HΦ
    icases Hi1 with ⟨%hd, %l, %Hl1, Hhd, Hil⟩
    wp_rec
    isimp [Hl1]
    wp_load
    wp_load
    wp_pures
    wp_bind &append _ _
    iapply ih _ _ ys $$ [$]
    iintro !> %l' Hil'
    wp_store
    wp_pures
    imodintro
    iapply HΦ
    iexists hd, l'
    iframe
    itrivial

-- We will implement reverse using a helper function called
-- [reverse_append], which takes two arguments, [l] and [acc], and
-- returns the list [rev l ++ acc].
def reverseAppend : Val := hl_val%
  rec reverse_append l acc :=
    match l with
    | none() => acc
    | some(hd) =>
      let x := fst(!hd);
      let l' := snd(!hd);
      hd ← (x, acc);
      reverse_append l' l

-- When [acc] is the empty list, it should thus simply return the reverse
-- of [l].
def reverse : Val := hl_val%
  λl, &reverseAppend l (none())

theorem reverse_append_spec (l acc : Val) (xs ys : List Val) :
    {{ (isList l xs : IProp GF) ∗ isList acc ys }}
      hl(&reverseAppend &l &acc)
    {{ v, RET v; isList v (xs.reverse ++ ys) }} := by
  induction xs generalizing l acc ys with
  | nil =>
    simp only [List.reverse_nil, List.nil_append, isList]
    iintro %Φ ⟨%Hll, Hla⟩ HΦ
    wp_rec
    isimp [Hll]
    wp_pures
    imodintro
    iapply HΦ $$ Hla
  | cons x xs ih =>
    simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append, isList]
    iintro %Φ ⟨⟨%hd, %l', %Hl, Hhd, Hll'⟩, H⟩ HΦ
    wp_rec
    isimp [Hl]
    wp_pures
    wp_load
    wp_load
    wp_store
    wp_pures
    iapply ih l' _ (x::ys) $$ [Hll' Hhd H]
    · iframe
      ieval (unfold isList)
      iexists hd, acc
      iframe
      ipureintro
      rfl
    · imodintro
      iexact HΦ

-- Now, we use the specification of [reverse_append] to prove the
-- specification of [reverse].
theorem reverse_spec (l : Val) (xs : List Val) :
    {{ (isList l xs : IProp GF) }}
      hl(&reverse &l)
    {{ v, RET v; isList v xs.reverse }} := by
  unfold reverse
  iintro %Φ Hll HΦ
  wp_pures
  iapply reverse_append_spec _ _ xs [] $$ [Hll]
  · iframe
    iunfold isList
    itrivial
  · isimp
    iframe

-- The specifications thus far have been rather straightforward. Now we
-- will show a very general specification for [fold_right].
def foldRight : Val := hl_val%
  rec fold_right f v l :=
    match l with
    | none() => v
    | some(hd) =>
      let x := fst(!hd);
      let l' := snd(!hd);
      f x (fold_right f v l')

-- The following specification has a lot of moving parts, so let us go
-- through them one by one.
-- - [l] is a linked list representing [xs], as seen by [isList l xs] in
--   the precondition.
-- - [P] is a predicate which all the values in [xs] should satisfy. This
--   is written as [[∗ list] x ∈ xs, P x]. It is a recursively defined
--   predicate, defined as follows:
--     [[∗ list] x ∈ [], P x := True]
--     [[∗ list] x ∈ x0 :: xs, P x := P x0 ∗ [∗ list] x ∈ xs, P x]
-- - [I] is a predicate (think [I] for invariant) describing the relation
--   between a list and the result of the fold.
-- - [a] is the base value, so fold will return [a] for the empty list;
--   this is captured by [I [] a].
-- - [f] is the folding function, which we assume satisfies:
--     [{{{ P x ∗ I ys a' }}} f x a' {{{ r, RET; I (x :: ys) r }}}].
--   Intuitively, this says that if [f] is applied to an argument from
--   the list (hence satisfying [P]) and [a'] is the result of folding
--   [ys], captured by [I ys a'], then the result [r] will be the result
--   of folding f over [x :: ys], captured by [I (x :: ys) r] in the
--   postcondition.
-- - The result [r] of folding must then satisfy [I xs r].
-- - Importantly, we do not change the original list. So we put
--   [isList l xs] in the postcondition.
--
-- Note that Hoare triples are persistent, and persistent predicates are
-- closed under universal quantification. Hence, in the proof, the
-- assumption for [f] will move into the persistent context.
theorem fold_right_spec (P : Val → IProp GF) (I : List Val → Val → IProp GF)
    (f a l : Val) (xs : List Val) :
    {{
      (isList l xs : IProp GF) ∗ ([∗list] x ∈ xs, P x) ∗ I [] a ∗
      (∀ (x a' : Val) ys,
        {{ P x ∗ I ys a' }} hl(&f &x &a') {{ r, RET r; I (x :: ys) r }})
    }}
      hl(&foldRight &f &a &l)
    {{ r, RET r; isList l xs ∗ I xs r}} := by
  induction xs generalizing a l with
  | nil =>
    simp [isList]
    iintro %Φ ⟨%Hl, e, HI, HP⟩ HΦ {e}
    iunfold foldRight
    isimp [Hl]
    wp_pures
    imodintro
    iapply HΦ
    iframe HI %Hl
  | cons x xs ih =>
    simp [isList]
    iintro %Φ ⟨⟨%hd, %l', %Hl, Hhd, Hll'⟩, ⟨HPx, HPxs⟩, HI, #HPI⟩ HΦ
    wp_rec
    isimp [Hl]
    wp_load
    wp_load
    wp_pures
    wp_bind &foldRight _ _ _
    iapply ih $$ [HI HPxs Hll' HPI]
    · iframe
      iapply HPI
    · iintro !> %r' ⟨Hll', HI⟩
      iapply HPI $$ %_ %_ %xs [$]
      iintro !> %r HI
      iapply HΦ
      iframe
      itrivial

-- We can now sum over a list simply by folding an addition function over
-- it.

def sumList : Val := hl_val%
  λl,
    let f := (λx y, x + y);
    &foldRight f #0 l

theorem sum_list_spec (l : Val) (xs : List Int) :
    {{ (isList l ((λ x : Int => hl_val(#x)) <$> xs) : IProp GF) }}
      hl(&sumList &l)
    {{ RET hl_val(#(List.foldr Int.add 0 xs : Int));
      isList l ((λ x : Int => hl_val(#x)) <$> xs) }} := by
  iintro %Φ Hl HΦ
  wp_rec; wp_pures
  let P (x : Val) : IProp GF := iprop% ∃i: Int, ⌜x = hl_val(#i)⌝
  let I (xs : List Val) (y : Val) : IProp GF := iprop%
    ∃ ys, ⌜xs = (λ x : Int => hl_val(#x)) <$> ys⌝ ∗
      ⌜y = hl_val(#(List.foldr Int.add 0 ys : Int))⌝
  iapply fold_right_spec P I (xs := ((λ x : Int => hl_val(#x)) <$> xs)) $$ [Hl]
  · iframe
    isplit
    · unfold P
      simp [Functor.map, BI.BigSepL.bigSepL_map]
      iapply BI.BigSepL.bigSepL_intro (P := iprop% □True)
      · iintro %_ %x %_ _
        iexists x
        itrivial
      · itrivial
    isplit
    · iexists []
      isimp [Functor.map, List.map_nil]
      itrivial
    · iunfold P, I
      iintro %x %a' %ys !> %Φ ⟨⟨%i, %Hxi⟩, ⟨%ys', %Hys, %Ha⟩⟩ HΦ
      isimp [Hxi, Ha]
      wp_pures
      imodintro
      iapply HΦ
      iexists i::ys'
      isimp [Hxi, Hys, Functor.map, List.map_cons]
      itrivial
  · iintro !> %r ⟨Hl, HI⟩
    isimp [I] at HI
    icases HI with ⟨%ys, %He1, %He2⟩
    have : xs = ys :=
      (List.map_inj_right fun x y e => BaseLit.int.inj (Val.lit.inj e)).mp He1
    ieval (rewrite [He2, ←this])
    iapply HΦ $$ Hl

end linked_lists
