-- ============================================================
-- § 5. Sorted Lists
-- ============================================================

/-!
# Sorted Lists in Lean 4

We follow the same three-stage pattern as with BSTs:
1. **Plain sort** — insertion sort with no invariants
2. **Extrinsic verification** — sortedness as a separate `Prop`, with proofs
3. **Intrinsic verification** — the type itself enforces ordering

We specialise to `Nat` so that `omega` can close all arithmetic goals
(the BST code could stay generic because it never needed transitivity
or symmetry of `compare`; sorted-list proofs do).
-/

-- ============================================================
-- § 5a. Plain insertion sort
-- ============================================================

@[simp] def natInsert (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys =>
    if x < y then x :: y :: ys
    else if x = y then y :: ys
    else y :: natInsert x ys

def insertionSort (xs : List Nat) : List Nat :=
  xs.foldl (fun acc x => natInsert x acc) []

#eval insertionSort [5, 3, 8, 1, 4]       -- [1, 3, 4, 5, 8]
#eval insertionSort [9, 2, 7, 1, 5, 3]    -- [1, 2, 3, 5, 7, 9]
#eval insertionSort []                     -- []
#eval insertionSort [42]                   -- [42]

-- ============================================================
-- § 5b. Extrinsic verification
-- ============================================================

/-
With extrinsic verification we:
  • Write the code first (§ 5a above).
  • Define what "sorted" means as a separate proposition.
  • Prove that our operations produce sorted output.
-/

-- Adjacent-pair strict ascending order.
-- Using a standalone name avoids clashing with anything in the std library.
@[simp] def Ascending : List Nat → Prop
  | []  => True
  | [_] => True
  | x :: y :: ys => x < y ∧ Ascending (y :: ys)

-- ---- Concrete proofs ----

/-
Hand-built sorted list, proved correct.

    [1, 3, 5, 7, 9]

`simp` unfolds `Ascending` on the concrete list, reducing it to
`1 < 3 ∧ 3 < 5 ∧ 5 < 7 ∧ 7 < 9 ∧ True`, and `omega` closes
every arithmetic goal.
-/
def sortedExample : List Nat := [1, 3, 5, 7, 9]

theorem sortedExample_ascending : Ascending sortedExample := by
  unfold sortedExample; simp [Ascending]; omega

-- A wrong list — uncomment to see the proof fail:
-- theorem bad_ascending : Ascending [1, 5, 3, 7] := by
--   unfold Ascending; simp; omega   -- omega cannot prove 5 < 3

-- ---- General theorems ----

/-- Insertion into an ascending list preserves `Ascending`. -/
@[simp] theorem natInsert_ascending {x : Nat} {xs : List Nat}
    (h : Ascending xs) : Ascending (natInsert x xs) := by
  match xs with
  | [] => simp
  | [y] =>
    simp only [natInsert, Ascending]
    split <;> split <;> simp_all <;> omega
  | y :: z :: zs =>
    simp [Ascending] at h
    obtain ⟨hyz, hsorted⟩ := h
    simp only [natInsert]
    split
    · -- x < y  →  x :: y :: z :: zs
      simp [Ascending, hyz, hsorted]; omega
    · split
      · -- x = y  →  list unchanged
        simp [Ascending, hyz, hsorted]
      · -- x > y  →  y :: natInsert x (z :: zs)
        simp [Ascending]
        constructor
        · -- y < head (natInsert x (z :: zs))
          -- Unfold one level of natInsert on (z :: zs) and case-split:
          --   • x < z  →  head is x  →  need y < x  (omega: ¬x<y ∧ ¬x=y → y<x)
          --   • x = z  →  head is z  →  need y < z  (have hyz)
          --   • x > z  →  head is z  →  need y < z  (have hyz)
          simp only [natInsert]
          split <;> [skip; split] <;> omega
        · exact natInsert_ascending hsorted

/-- Insertion sort produces ascending output. -/
theorem insertionSort_ascending (xs : List Nat) :
    Ascending (insertionSort xs) := by
  unfold insertionSort
  -- Strengthen to: for any already-ascending accumulator, the fold
  -- preserves `Ascending`.
  suffices ∀ acc, Ascending acc →
      Ascending (xs.foldl (fun a x => natInsert x a) acc) from
    this [] trivial
  intro acc hacc
  induction xs generalizing acc with
  | nil => exact hacc
  | cons x xs ih => exact ih (natInsert_ascending hacc)

-- ---- The extrinsic wrapper ----

/-
We bundle a `List Nat` with a proof of `Ascending`, mirroring `BSTree`.
-/

def SortedNatList := { xs : List Nat // Ascending xs }

def SortedNatList.empty : SortedNatList :=
  ⟨[], trivial⟩

def SortedNatList.insert (x : Nat) (s : SortedNatList) : SortedNatList :=
  ⟨natInsert x s.val, natInsert_ascending s.property⟩

def SortedNatList.toList (s : SortedNatList) : List Nat :=
  s.val

def SortedNatList.ofList (xs : List Nat) : SortedNatList :=
  ⟨insertionSort xs, insertionSort_ascending xs⟩

-- Usage:
#eval (SortedNatList.empty.insert 5 |>.insert 1 |>.insert 3).toList
  -- [1, 3, 5]

#eval (SortedNatList.ofList [9, 2, 7, 1, 5, 3]).toList
  -- [1, 2, 3, 5, 7, 9]

-- ---- Manually built + proved ascending ----

def handSorted : SortedNatList :=
  ⟨[2, 5, 7, 12, 99], by simp [Ascending]; omega⟩

#eval handSorted.toList   -- [2, 5, 7, 12, 99]

-- A wrong manual list — uncomment to see it fail:
-- def badSorted : SortedNatList :=
--   ⟨[2, 5, 3, 12], by simp [Ascending]; omega⟩   -- fails!

-- ============================================================
-- § 5c. Intrinsic verification
-- ============================================================

/-
With intrinsic verification the *type itself* forbids unsorted lists.

The key idea: `OrdList lb` is a sorted list whose elements are all
greater than the optional lower bound `lb`.

  • `OrdList none`       — no lower bound (a fresh sorted list)
  • `OrdList (some n)`   — every element must be > `n`

When we cons a value `v`, the tail becomes `OrdList (some v)`,
automatically enforcing that all subsequent elements are larger.

Compare with the BST approach where a *predicate* `P` accumulated
constraints.  Here an `Option Nat` bound plays the same role but is
simpler for the linear structure of a list.
-/

def Bounded (lb : Option Nat) (v : Nat) : Prop :=
  match lb with
  | none   => True
  | some b => b < v

inductive OrdList : Option Nat → Type where
  | nil  : OrdList lb
  | cons : (v : Nat) → Bounded lb v → OrdList (some v) → OrdList lb

-- A sorted list with no lower bound.
abbrev SortedOrdList := OrdList none

/-
`insert` takes a value `x` together with a proof that `x` respects
the current lower bound.  For a `SortedOrdList` the bound is `none`,
so this proof is just `trivial`.
-/
def OrdList.insert (x : Nat) (hx : Bounded lb x) :
    OrdList lb → OrdList lb
  | .nil => .cons x hx .nil
  | .cons v hv tail =>
    if hlt : x < v then
      -- x goes before v; the proof `hlt` shows `Bounded (some x) v`.
      .cons x hx (.cons v hlt tail)
    else if _ : x = v then
      -- duplicate — keep the original
      .cons v hv tail
    else
      -- x > v — recurse into the tail; omega derives `v < x`.
      .cons v hv (tail.insert x (show Bounded (some v) x by
        simp [Bounded]; omega))

def OrdList.toList : OrdList lb → List Nat
  | .nil        => []
  | .cons v _ t => v :: t.toList

-- For a `SortedOrdList` the bound is `none`, so every proof is `trivial`.
def mySortedOrd : SortedOrdList :=
  OrdList.nil
    |>.insert 4 trivial
    |>.insert 2 trivial
    |>.insert 6 trivial
    |>.insert 1 trivial
    |>.insert 3 trivial

#eval mySortedOrd.toList   -- [1, 2, 3, 4, 6]

-- ---- A restricted list: all elements > 10 ----

/-
By starting with `OrdList (some 10)` we get a list that only accepts
values above 10.  The proof obligation at each insert is `10 < x`,
which `omega` dispatches on concrete numbers.
-/
def above10 : OrdList (some 10) :=
  OrdList.nil
    |>.insert 15 (by simp [Bounded]; omega)
    |>.insert 12 (by simp [Bounded]; omega)
    |>.insert 20 (by simp [Bounded]; omega)

#eval above10.toList   -- [12, 15, 20]

-- Uncomment to see it fail — 5 is not above 10:
-- def bad10 : OrdList (some 10) :=
--   OrdList.nil |>.insert 5 (by simp [Bounded]; omega)  -- omega can't prove 10 < 5
