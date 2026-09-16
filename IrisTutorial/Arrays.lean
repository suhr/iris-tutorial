import Iris.HeapLang

namespace Arrays
open Iris HeapLang

-- # Arrays

-- In the Linked List chapter, we saw that we could use references to
-- implement a list data structure. However, HeapLang also supports
-- arrays that we can use for this purpose. The expression [AllocN n v]
-- allocates [n] contiguous copies of [v] and returns the location of the
-- first element. We then access a specific value by calculating its
-- offset [l +ₗ i] from the first element. This results in a location
-- which we can load from or write to.

-- ## Copy

section proofs
variable [HeapLangGS hlc GF]

-- To see arrays in action, let's implement a function, [copy], that
-- copies an array while keeping the original intact. We define it in
-- terms of a more general function, [copy_to].

def copy_to : Val := hl_val%
  rec copy_to src dst len :=
    if len = #0 then #()
    else (
      dst ← !src;
      copy_to (src +ₗ #1) (dst +ₗ #1) (len - #1))

def copy : Val := hl_val%
  λ src len,
    let dst := allocn(len, #());
    &copy_to src dst len;
    dst

-- Just as with [isList], arrays have a predicate we can use, written
-- [l ↦∗ vs]. Here, [l] is the location of the first element in the array,
-- and [vs] is the list of values currently stored at each location of
-- the array.

theorem copy_to_spec (a1 a2 : Loc) (l1 l2 : List Val) :
    {{ (a1 ↦∗ l1 : IProp GF) ∗ a2 ↦∗ l2 ∗ ⌜l1.length = l2.length⌝ }}
      hl(&copy_to #a1 #a2 #(l1.length ))
    {{ RET hl_val(#()); a1 ↦∗ l1 ∗ a2 ↦∗ l1 }} := by
  iintro %Φ ⟨H1, H2, %H⟩ HΦ
  iloeb as ih generalizing %a1 %a2 %l1 %l2 %H
  match l1, l2 with
  | .nil, .nil =>
    wp_rec; wp_pures
    isimp; wp_pures
    iapply HΦ
    iframe
  | .nil, .cons _ _ => simp at H
  | .cons _ _, .nil => simp at H
  | .cons x xs, .cons y ys =>
    wp_rec; wp_pures
    have : (hl_val(#(↑xs.length + 1 : Int)) == hl_val(#0)) = false := by
      grind only
    isimp [this]; wp_pures
    -- For the cons case, we can use [array_cons] to split the array into
    -- a mapsto on the first location, with the remaining array starting
    -- at the next location.
    icases array_cons.mp $$ H1 with ⟨Hx, Hxs⟩
    icases array_cons.mp $$ H2 with ⟨Hy, Hys⟩
    wp_load
    wp_store
    wp_pures
    isimp
    iapply ih $$ %(a1 + 1) %(a2 + 1) %xs %ys %(by simp at H; exact H) Hxs Hys
    iintro !> ⟨Hxs, Hys⟩
    icombine Hx Hxs as H1
    icombine Hy Hys as H2
    icases array_cons.mpr $$ H1 with H1
    icases array_cons.mpr $$ H2 with H2
    iapply HΦ
    iframe

-- When allocating arrays, HeapLang requires the size to be greater than
-- zero. So we add this to our precondition.
theorem copy_spec (a : Loc) (l : List Val) :
    {{ (a ↦∗ l : IProp GF) ∗ ⌜0 < l.length⌝ }}
      hl(&copy #a #(l.length))
    {{ (a' : Loc), RET hl_val(#a'); a ↦∗ l ∗ a' ↦∗ l }} := by
  iintro %Φ ⟨Ha, %H⟩ HΦ
  wp_lam; wp_pures
  wp_alloc a' with Ha'
  wp_pures
  isimp at Ha'
  wp_apply copy_to_spec a a' l (List.replicate l.length hl_val(#())) $$ [Ha Ha']
  · isimp only [List.length_replicate]
    iframe
  iintro ⟨Ha, Ha'⟩
  wp_pures
  iapply HΦ
  iframe


-- ## Increment

-- As arrays can be thought of as a type of list, we can re-implement
-- some of the functions we wrote for linked lists. For instance, the
-- increment function.
def inc : Val := hl_val%
  rec inc arr len :=
    if len = #0 then #()
    else (
      arr ← !arr + #1;
      inc (arr +ₗ #1) (len - #1))

set_option warn.sorry false in
theorem inc_spec (a : Loc) (l : List Int) :
    {{ (a ↦∗ (fun i : Int => hl_val(#i)) <$> l : IProp GF) }}
      hl(&inc #a #(l.length))
    {{ RET hl_val(#()); a ↦∗ (fun i : Int => hl_val(#(i + 1 : Int))) <$> l }} := by
  -- (exercise)
  sorry


-- ## Reverse

-- Another common list operation is reversing the list. One way of
-- reversing an array is by swapping the first and last elements of the
-- array, and recursively repeating this process on the remaining array.
def reverse : Val := hl_val%
  rec reverse arr len :=
    if len ≤ #1 then #()
    else (
      let last := arr +ₗ (len - #1);
      let tmp := !arr;
      arr ← !last;
      last ← tmp;
      reverse (arr +ₗ #1) (len - #2))

-- Notice we are not following structural induction on the list of values
-- as we remove elements from both the front and the back. As such, you
-- need to use either löb induction or strong induction on the size of
-- the list.
set_option warn.sorry false in
theorem reverse_spec (a : Loc) (l : List Val) :
    {{ (a ↦∗ l : IProp GF) }}
      hl(&reverse #a #(l.length))
    {{ RET hl_val(#()); a ↦∗ l.reverse }} := by
  -- (exercise)
  sorry

end proofs
