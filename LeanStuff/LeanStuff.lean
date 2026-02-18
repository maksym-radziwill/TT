-- This module serves as the root of the `LeanStuff` library.
-- Import modules here that should be built as part of the library.
import LeanStuff.Basic

/-!
# Binary Search Trees in Lean 4

We build a binary search tree in three stages:
1. **Plain tree** — an unverified recursive data structure
2. **Extrinsic verification** — we define the BST invariant as a separate `Prop`
   and prove that operations preserve it, then bundle tree + proof into a subtype.
3. **Intrinsic verification** — we index the tree type itself by a predicate,
   making it impossible to even *construct* a tree that violates the invariant.
-/

-- ============================================================
-- § 1. Plain binary tree
-- ============================================================

inductive Tree : (α : Type) → Type where
  | leaf : Tree α
  | node : (left : Tree α) → (val : α) → (right : Tree α) → Tree α

-- Size is always non-negative, so we use `Nat` rather than `Int`.
def Tree.size (t : Tree α) : Nat :=
  match t with
  | .leaf => 0
  | .node left _ right => 1 + left.size + right.size

-- In-order traversal.
def Tree.toList (t : Tree α) : List α :=
  match t with
  | .leaf => []
  | .node left val right => left.toList ++ [val] ++ right.toList

-- Insert into a binary search tree.
-- NOTE: the pattern binds `left` first, then `val`, then `right`,
-- matching the order declared in the `node` constructor.
@[simp] def Tree.insert [Ord α] (t : Tree α) (el : α) : Tree α :=
  match t with
  | .leaf => .node .leaf el .leaf
  | .node left cur right =>
    match compare el cur with
    | .lt => .node (left.insert el) cur right
    | .eq => .node left cur right
    | .gt => .node left cur (right.insert el)

-- ============================================================
-- § 2. Extrinsic verification
-- ============================================================

/-
With extrinsic verification we:
  • Write the code first (§ 1 above).
  • Define what "correct" means as a separate proposition.
  • Prove that our operations preserve correctness.
-/

-- `ForAll P t` holds when `P` is true for every value stored in `t`.
@[simp] def Tree.ForAll (P : α → Prop) : Tree α → Prop
  | .leaf       => True
  | .node l v r => P v ∧ l.ForAll P ∧ r.ForAll P

-- The BST invariant: every value in the left subtree compares less than the
-- root, every value in the right subtree compares greater, and both subtrees
-- are themselves BSTs.
@[simp] def Tree.BST [Ord α] : Tree α → Prop
  | .leaf       => True
  | .node l v r =>
    l.ForAll (fun x => compare x v = .lt) ∧
    r.ForAll (fun x => compare x v = .gt) ∧
    l.BST ∧
    r.BST

-- Inserting a value that satisfies `P` into a tree where `ForAll P` holds
-- preserves the `ForAll P` property.
--
-- The explicit `(x : α)` makes clear where the universally quantified
-- variable comes from; Lean can infer it, but naming it aids readability.
@[simp] theorem Tree.ForAll_insert [Ord α] {P : α → Prop} {t : Tree α} {x : α}
    (hx : P x) (ht : t.ForAll P) : (t.insert x).ForAll P := by
  match t with
  | .leaf => simp_all
  | .node left val right =>
    simp_all
    match compare x val with
    | .lt =>
        simp_all
        exact ForAll_insert hx ht.2.1
    | .gt =>
        simp_all
        exact ForAll_insert hx ht.2.2
    | .eq => simp_all

-- Insertion preserves the BST invariant.
@[simp] theorem Tree.BST_insert [Ord α] {t : Tree α} {x : α}
    (h : t.BST) : (t.insert x).BST := by
  match t with
  | .leaf =>
    simp_all
  | .node left val right =>
    simp_all
    obtain ⟨h1, h2, h3, h4⟩ := h
    match hc : compare x val with
    | .lt =>
      simp_all
      exact Tree.BST_insert h3
    | .gt =>
      simp_all
      exact Tree.BST_insert h4
    | .eq =>
      simp_all

/-
### The extrinsic wrapper

We bundle a `Tree` together with a proof that it satisfies `BST` using a
subtype `{ t : Tree α // t.BST }`.  This lets callers work with a "proven
correct" tree without thinking about proofs at each call site.
-/

def BSTree (α : Type) [Ord α] := { t : Tree α // t.BST }

def BSTree.empty [Ord α] : BSTree α :=
  ⟨.leaf, trivial⟩

def BSTree.insert [Ord α] (x : α) (t : BSTree α) : BSTree α :=
  ⟨t.val.insert x, Tree.BST_insert t.property⟩

-- Delegate `toList` through the wrapper so the type is actually usable.
def BSTree.toList [Ord α] (t : BSTree α) : List α :=
  t.val.toList

-- Delegate `size` through the wrapper.
def BSTree.size [Ord α] (t : BSTree α) : Nat :=
  t.val.size

-- ============================================================
-- § 3. Intrinsic verification
-- ============================================================

/-
With intrinsic verification the *type itself* forbids ill-formed trees.

The key idea: `BTree α P` is a BST whose values all satisfy predicate `P`.
As we descend into a subtree the predicate gets *strengthened* with an
ordering constraint:

  • Left  child of a node with value `v`:  `fun x => P x ∧ compare x v = .lt`
  • Right child of a node with value `v`:  `fun x => P x ∧ compare x v = .gt`

This means ordering invariants accumulate automatically in the type — there
is no separate `BST` proposition to maintain.
-/

inductive BTree (α : Type) [Ord α] : (α → Prop) → Type where
  | leaf : BTree α P
  | node : (v : α) → P v
         → BTree α (fun x => P x ∧ compare x v = .lt)
         → BTree α (fun x => P x ∧ compare x v = .gt)
         → BTree α P

-- A `SortedTree` starts with the trivially-true predicate; the only
-- constraints that accumulate are the ordering ones from `node`.
abbrev SortedTree (α : Type) [Ord α] := BTree α (fun _ => True)

/-
Notice that `insert` doesn't just take a value `x` — it also takes
`hx : P x`, a *proof* that `x` belongs in this tree.

For a `SortedTree`, `P` is `fun _ => True` ("anything goes"), so this
proof is trivially satisfied and you never think about it.

But suppose you had a tree that only stores positive numbers, so `P`
is `fun x => x > 0`. Then calling `insert (-3) proof_that_neg3_gt_0`
wouldn't even compile — you can't produce that proof.  The type system
stops you from inserting bad data before the code ever runs.
-/
def BTree.insert [Ord α] (x : α) (hx : P x) :
    BTree α P → BTree α P
  | .leaf => .node x hx .leaf .leaf
  | .node v hv left right =>
    match hc : compare x v with
    | .lt => .node v hv (left.insert x ⟨hx,hc⟩) right
    | .eq => .node v hv left right
    | .gt => .node v hv left (right.insert x ⟨hx, hc⟩)


--- Sorted Lists

/-
With intrinsic verification the *type itself* forbids unsorted lists.

Unlike `BTree`, which indexes by a predicate `P`, we index by a
`Nat` lower bound.  `SList lb` is a sorted list whose elements are
all ≥ `lb`:

  • `SList n`  — every element is ≥ `n`, and only values ≤ `n` can
                  be consed in front (since `cons` requires `new ≤ old`)
  • `SList 0`  — the most restrictive case: nothing except 0 can be
                  directly prepended

When we cons a value `v`, the tail becomes `SList v`, automatically
enforcing that all subsequent elements are at least `v`.

The last argument `any ≤ new` (or `any ≤ x` in `singleton`) acts as a
type-cast: it lets us produce an `SList any` for any `any` that is at
most the head element.  Without it, `cons` could only return `SList new`,
but during insertion we need to return `SList (min lb x)`, which may be
smaller than the head.  The proof witness bridges that gap.
-/

inductive SList : Nat → Type where
  | singleton : (x : Nat) → (any ≤ x) → SList any
  | cons : (new : Nat) → new ≤ old → SList old → (any ≤ new) → SList any

-- Bonus HW: Find the function.
def SList.insert (x : Nat) (l : SList lb) : SList (min lb x) :=
  by sorry

def SList.toList (l : SList v) : List Nat :=
  match l with
  | .singleton v _ => [v]
  | .cons new _ old _ => [new] ++ old.toList

-- Minor Issue: With SList 0 as a return type we
-- can no longer append to the list.
def List.fromList (l : List Nat) : SList 0 :=
  match l with
  | v :: xs =>
    xs.foldr (fun x acc =>
       acc.insert x
    ) (.singleton v (by omega))

  | [] => .singleton 0 (by omega) -- This is ugly

def test := [1,2,10,3].fromList

-- #eval test.toList

def ex := SList.singleton (any := 2) 2 (by grind) |> SList.insert 5 |> SList.insert 6 |> SList.insert 7

-- #eval ex.toList

-- #eval ex
