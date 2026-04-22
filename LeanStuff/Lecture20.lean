/-
  Lecture 20: Internal Verification
  Companion Lean 4 file

  This file contains every definition and theorem from
  the lecture slides. Code that intentionally does NOT
  typecheck is commented out with an explanation.
-/

namespace Lec20

-- ============================================================
-- Prerequisites from Lecture 19
-- ============================================================

inductive N : Type where
  | zero : N
  | succ : N → N
deriving Repr

inductive MyList (A : Type) : Type where
  | nil  : MyList A
  | cons : A → MyList A → MyList A

-- Addition: recurs on the SECOND argument (Lecture 19 version)
def add : N → N → N
  | m, .zero   => m
  | m, .succ k => .succ (add m k)

-- Theorems about add (proved in Lecture 19)
theorem add_zero (m : N) : add m .zero = m := rfl

theorem zero_add (m : N) : add .zero m = m := by
  induction m with
  | zero      => rfl
  | succ k ih =>
    show N.succ (add .zero k) = N.succ k
    rw [ih]

theorem succ_add (m k : N) : add (.succ m) k = .succ (add m k) := by
  induction k with
  | zero      => rfl
  | succ k ih =>
    show N.succ (add (.succ m) k) = N.succ (N.succ (add m k))
    rw [ih]

-- Addition: recurs on the FIRST argument (for vappend)
def add' : N → N → N
  | .zero,   n => n
  | .succ m, n => .succ (add' m n)

-- MyList operations (for external verification examples)
def MyList.length : MyList A → N
  | .nil       => .zero
  | .cons _ xs => .succ (MyList.length xs)

def MyList.map (f : A → B) : MyList A → MyList B
  | .nil       => .nil
  | .cons x xs => .cons (f x) (MyList.map f xs)

def MyList.append : MyList A → MyList A → MyList A
  | .nil,       ys => ys
  | .cons x xs, ys => .cons x (MyList.append xs ys)

-- External verification: proving map preserves length
theorem length_map (f : A → B) (xs : MyList A)
    : MyList.length (MyList.map f xs) = MyList.length xs := by
  induction xs with
  | nil         => rfl
  | cons x xs ih =>
    simp only [MyList.map, MyList.length]
    rw [ih]


-- ============================================================
-- Part II: Vectors
-- ============================================================

inductive Vec (A : Type) : N → Type where
  | nil  : Vec A .zero
  | cons {n : N} : A → Vec A n → Vec A (.succ n)

-- Building vectors
#check (Vec.nil : Vec Nat .zero)
#check (Vec.cons 3 Vec.nil : Vec Nat (.succ .zero))
#check (Vec.cons 1 (Vec.cons 2 (Vec.cons 3 Vec.nil))
        : Vec Nat (.succ (.succ (.succ .zero))))

-- Head: total by construction
-- The input type Vec A (.succ n) rules out nil.
def Vec.head : Vec A (.succ n) → A
  | .cons x _ => x


-- Tail
def Vec.tail : Vec A (.succ n) → Vec A n
  | .cons _ xs => xs

-- Map: preserves length by construction
def Vec.vmap (f : A → B) : Vec A n → Vec B n
  | .nil       => .nil
  | .cons x xs => .cons (f x) (Vec.vmap f xs)

-- Zip: shared index n forces equal lengths
def Vec.vzip : Vec A n → Vec B n → Vec (A × B) n
  | .nil,       .nil       => .nil
  | .cons x xs, .cons y ys => .cons (x, y) (Vec.vzip xs ys)

-- --------------------------------------------------------
-- Append: the definitional equality issue
-- --------------------------------------------------------

-- Using add' (recurs on FIRST arg): typechecks directly!
-- add' .zero n ≡ n  (ι fires)
-- add' (.succ m) n ≡ .succ (add' m n)  (ι fires)

def Vec.vappend : Vec A m → Vec A n → Vec A (add' m n)
  | .nil,       ys => ys
  | .cons x xs, ys => .cons x (Vec.vappend xs ys)

-- Using add (recurs on SECOND arg): DOES NOT typecheck.
-- Uncomment to see the error:
--def Vec.vappend_bad : Vec A m → Vec A n → Vec A (add m n)
 --  | .nil,       ys => ys   -- ERROR: type mismatch
--       -- got:      Vec A n
--       -- expected: Vec A (add .zero n)
--       -- add .zero n does not reduce (ι stuck on n)
 --  | .cons x xs, ys => .cons x (Vec.vappend_bad xs ys)

-- --------------------------------------------------------
-- Bridging the gap with tactic mode
-- --------------------------------------------------------

-- Append using add (second-arg recursion) with rw to bridge the gap
def Vec.vappend' : Vec A m → Vec A n → Vec A (add m n)
  | .nil, ys => by
    -- goal: Vec A (add .zero n)
    rw [zero_add]
    -- goal: Vec A n
    exact ys
  | .cons x xs, ys => by
    -- goal: Vec A (add (.succ _) n)
    rw [succ_add]
    -- goal: Vec A (.succ (add _ n))
    exact .cons x (Vec.vappend' xs ys)

-- Replicate: always smooth
def Vec.replicate : (n : N) → A → Vec A n
  | .zero,   _ => .nil
  | .succ k, a => .cons a (Vec.replicate k a)


-- ============================================================
-- Part III: Sigma Types
-- ============================================================

-- Dependent pair: B is A → Type, not A → Prop.
-- The second component is DATA (e.g., a Vec), not a proof.
-- (For A → Prop, Lean has Subtype, written { x // P x }.)
structure DSigma (A : Type) (B : A → Type) where
  fst : A
  snd : B fst

-- Filtering a vector: output length is unknown,
-- so we return it existentially via a sigma type.
def Vec.vfilter (p : A → Bool) : Vec A n → DSigma N (Vec A)
  | .nil => ⟨.zero, .nil⟩
  | .cons x xs =>
    let ⟨k, ys⟩ := Vec.vfilter p xs
    match p x with
    | true  => ⟨.succ k, .cons x ys⟩
    | false => ⟨k, ys⟩

-- Quick test
#eval
  let v := Vec.cons 1 (Vec.cons 2 (Vec.cons 3 (Vec.cons 4 Vec.nil)))
  let result := Vec.vfilter (fun n => n % 2 == 0) v
  result.fst  -- should be 2 (two even numbers)


-- ============================================================
-- Part IV: Internally Verified Binary Search Trees
-- ============================================================

-- Unverified tree (for contrast)
inductive Tree (A : Type) : Type where
  | leaf : Tree A
  | node : Tree A → A → Tree A → Tree A

-- Invalid tree: 5 on the left of 3 — type allows it!
#check Tree.node
  (Tree.node Tree.leaf 5 Tree.leaf)
  3
  Tree.leaf
-- This typechecks even though it violates the BST property.

-- --------------------------------------------------------
-- Boolean comparison on N
-- --------------------------------------------------------

-- Returns Lean's Bool so we can use if-then-else and
-- dependent pattern matching (match h : ...) directly.
def N.ble : N → N → Bool
  | .zero,   _       => true
  | .succ _, .zero   => false
  | .succ m, .succ n => N.ble m n

-- Quick sanity checks
#eval N.ble .zero (.succ .zero)                          -- true
#eval N.ble (.succ (.succ .zero)) (.succ .zero)          -- false
#eval N.ble (.succ .zero) (.succ (.succ (.succ .zero)))  -- true

-- --------------------------------------------------------
-- Bounds: extend N with -∞ and +∞
-- --------------------------------------------------------

inductive Bound : Type where
  | bot : Bound    -- -∞
  | val : N → Bound
  | top : Bound    -- +∞

def Bound.ble : Bound → Bound → Bool
  | .bot,   _      => true
  | _,      .top   => true
  | .val m, .val n => N.ble m n
  | _, .bot => false
  | .top, .val _ => false


-- --------------------------------------------------------
-- The verified BST, indexed by lower and upper bounds
-- --------------------------------------------------------

inductive BST : Bound → Bound → Type where
  | leaf : BST lo hi
  | node : (k : N)
         → Bound.ble lo (.val k) = true
         → Bound.ble (.val k) hi = true
         → BST lo (.val k)
         → BST (.val k) hi
         → BST lo hi

-- A valid singleton BST: node with key 3, bounds -∞ to +∞
#check BST.node
  (.succ (.succ (.succ .zero)))  -- k = 3
  (rfl : Bound.ble .bot (.val (.succ (.succ (.succ .zero)))) = true)
  (rfl : Bound.ble (.val (.succ (.succ (.succ .zero)))) .top = true)
  BST.leaf
  BST.leaf

-- Invalid BST: 5 on the left of 3 — CANNOT be constructed.
-- Uncomment to see the error:
-- #check BST.node
--   (.succ (.succ (.succ .zero)))  -- k = 3
--   (rfl)  -- lo = bot ≤ 3 ✓
--   (rfl)  -- 3 ≤ top ✓
--   (BST.node
--     (.succ (.succ (.succ (.succ (.succ .zero)))))  -- k = 5
--     (rfl)  -- bot ≤ 5 ✓
--     (rfl)  -- NEED: N.ble 5 3 = true, but N.ble 5 3 = false ✗
--     BST.leaf
--     BST.leaf)
--   BST.leaf

-- --------------------------------------------------------
-- Searching the BST
-- --------------------------------------------------------

def BST.search (k : N) : BST lo hi → Bool
  | .leaf => false
  | .node k' _ _ left right =>
    if N.ble k k' then
      if N.ble k' k then true         -- k = k'
      else BST.search k left           -- k < k'
    else BST.search k right             -- k > k'

-- --------------------------------------------------------
-- Insertion into the BST
-- --------------------------------------------------------

-- Helper lemma: if N.ble a b = false, then N.ble b a = true.
-- (Full proof by induction on a and b.)
theorem ble_false_rev {a b : N} (h : N.ble a b = false)
    : N.ble b a = true := by
  induction a, b using N.ble.induct with
  | case1 b => simp [N.ble] at h       -- N.ble .zero b = true ≠ false
  | case2 a => simp [N.ble]            -- N.ble (.succ a) .zero = false → N.ble .zero (.succ a) = true
  | case3 a b ih =>                    -- inductive case
    simp [N.ble] at h ⊢
    exact ih h

--def test {k k'} (h : N.ble k k' = false): true = false := by
--  rw [ble_false_rev] at h
--  exact h

--  sorry

-- Dependent pattern match version of insert.
-- We match on the Bool result of N.ble k k' and bind
-- the equation as h, so we have a proof in each branch.
def BST.insert (k : N)
    (p1 : Bound.ble lo (.val k) = true)
    (p2 : Bound.ble (.val k) hi = true)
    : BST lo hi → BST lo hi
  | .leaf => .node k p1 p2 .leaf .leaf
  | .node k' q1 q2 left right =>
    match h : N.ble k k' with
    | true  =>
      -- h : N.ble k k' = true
      -- Bound.ble (.val k) (.val k') = N.ble k k' = true
      .node k' q1 q2 (BST.insert k p1 h left) right
    | false => by
      -- h : N.ble k k' = false
      -- ble_false_rev h : N.ble k' k = true
      -- which is Bound.ble (.val k') (.val k) = true
        --rw [ble_false_rev] at h
        have U := ble_false_rev h
        exact .node k' q1 q2 left (BST.insert k U p2 right)

-- --------------------------------------------------------
-- Internalizing membership: BST indexed by a set
-- --------------------------------------------------------

-- The type BST lo hi → BST lo hi does NOT guarantee contents:
def BST.discard : BST lo hi → BST lo hi
  | _ => .leaf

-- Better: index the BST by a membership predicate (N → Prop).
-- The predicate tracks which elements are in the tree.
inductive BSTM : Bound → Bound → (N → Prop) → Type where
  | leaf : BSTM lo hi (fun _ => False)
  | node : (k : N)
         → Bound.ble lo (.val k) = true
         → Bound.ble (.val k) hi = true
         → BSTM lo (.val k) memL
         → BSTM (.val k) hi memR
         → BSTM lo hi (fun x => memL x ∨ x = k ∨ memR x)

-- Example: a singleton tree containing 3
-- Its membership predicate is (fun x => False ∨ x = 3 ∨ False)
def singleton3 : BSTM .bot .top (fun x => False ∨ x = n3 ∨ False) :=
  .node n3 rfl rfl .leaf .leaf

-- Insert: the return type says exactly what it does.
-- The output contains everything the input had, plus k.
-- Uses @BSTM.node to bind memL/memR, and funext + simp for ∨ casts.
def BSTM.insert (k : N)
    (p1 : Bound.ble lo (.val k) = true)
    (p2 : Bound.ble (.val k) hi = true)
    : BSTM lo hi mem → BSTM lo hi (fun x => x = k ∨ mem x)
  | .leaf => by
    -- goal: BSTM lo hi (fun x => x = k ∨ False)
    -- .node k p1 p2 .leaf .leaf : BSTM lo hi (fun x => False ∨ x = k ∨ False)
    have : (fun x => x = k ∨ False) = (fun x => False ∨ x = k ∨ False) := by
      funext x; simp [or_comm, false_or]
    rw [this]
    exact .node k p1 p2 .leaf .leaf
  | @BSTM.node _ _ memL memR k' q1 q2 left right => by
    -- goal: BSTM lo hi (fun x => x = k ∨ (memL x ∨ x = k' ∨ memR x))
    match hc : N.ble k k' with
    | true =>
      -- insert k into left gives: BSTM lo (.val k') (fun x => x = k ∨ memL x)
      -- rebuild node: BSTM lo hi (fun x => (x = k ∨ memL x) ∨ x = k' ∨ memR x)
      -- need:         BSTM lo hi (fun x => x = k ∨ (memL x ∨ x = k' ∨ memR x))
      have : (fun x => x = k ∨ (memL x ∨ x = k' ∨ memR x))
           = (fun x => (x = k ∨ memL x) ∨ x = k' ∨ memR x) := by
        funext x; simp [or_assoc]
      rw [this]
      exact .node k' q1 q2 (BSTM.insert k p1 hc left) right
    | false =>
      -- insert k into right gives: BSTM (.val k') hi (fun x => x = k ∨ memR x)
      -- rebuild node: BSTM lo hi (fun x => memL x ∨ x = k' ∨ (x = k ∨ memR x))
      -- need:         BSTM lo hi (fun x => x = k ∨ (memL x ∨ x = k' ∨ memR x))
      have : (fun x => x = k ∨ (memL x ∨ x = k' ∨ memR x))
           = (fun x => memL x ∨ x = k' ∨ (x = k ∨ memR x)) := by
        funext x; simp [or_comm, or_left_comm]
      rw [this]
      exact .node k' q1 q2 left (BSTM.insert k (ble_false_rev hc) p2 right)

-- --------------------------------------------------------
-- Unverified insert (for contrast)
-- --------------------------------------------------------

def Tree.insert (k : N) : Tree N → Tree N
  | .leaf => .node .leaf k .leaf
  | .node left k' right =>
    if N.ble k k' then
      .node (Tree.insert k left) k' right
    else
      .node left k' (Tree.insert k right)

-- --------------------------------------------------------
-- Building a BST interactively
-- --------------------------------------------------------

-- Let's build a BST containing 2, 4, 1 (inserted in that order).
-- We abbreviate the Peano numerals:
def n0 : N := .zero
def n1 : N := .succ n0
def n2 : N := .succ n1
def n3 : N := .succ n2
def n4 : N := .succ n3
def n5 : N := .succ n4

-- Start with an empty tree (bounds: -∞ to +∞)
def t0 : BST .bot .top := .leaf

-- Insert 2
def t1 : BST .bot .top := BST.insert n2 rfl rfl t0

-- Insert 4
def t2 : BST .bot .top := BST.insert n4 rfl rfl t1

-- Insert 1
def t3 : BST .bot .top := BST.insert n1 rfl rfl t2

-- Search
#eval BST.search n4 t3   -- true
#eval BST.search n1 t3   -- true
#eval BST.search n5 t3   -- false

-- ============================================================
-- Exercises
-- ============================================================
-- Replace each `sorry` with a working definition or proof.

-- Exercise 1: Explain (in a comment) why the case
-- (.nil, .cons ...) is impossible in vzip. Then uncomment
-- and complete the definition.
def Vec.vzip' : Vec A n → Vec B n → Vec (A × B) n
   | .nil,       .nil       => sorry
   | .cons x xs, .cons y ys => sorry

-- Exercise 2: Flatten a vector of vectors.
-- Which definition of mul (on the first vs second argument)
-- makes this typecheck without casts?
def mul : N → N → N
  | _, .zero   => .zero
  | m, .succ k => add' (mul m k) m

def Vec.vconcat : Vec (Vec A m) n → Vec A (mul n m) :=
  sorry

-- Exercise 3: Convert a vector to a list.
-- Does this need any proofs? Why or why not?
def Vec.toList : Vec A n → MyList A :=
  sorry

-- Exercise 4: Try to build a BST node with k = 3,
-- lo = .val 5, hi = .top. Which proof obligation fails?
-- Uncomment to see the error:
-- #check (BST.node
--   (.succ (.succ (.succ .zero)))      -- k = 3
--   (sorry : Bound.ble (.val (.succ (.succ (.succ (.succ (.succ .zero)))))) (.val (.succ (.succ (.succ .zero)))) = true)
--   (sorry : Bound.ble (.val (.succ (.succ (.succ .zero)))) .top = true)
--   BST.leaf
--   BST.leaf : BST (.val (.succ (.succ (.succ (.succ (.succ .zero)))))) .top)

-- Exercise 5 (Harder): Define an internally verified sorted list.
-- A sorted list indexed by a lower bound, where each cons
-- carries a proof that the new element is ≥ the bound.
inductive SortedList : Bound → Type where
  | snil  : SortedList lo
  | scons : (k : N)
          → Bound.ble lo (.val k) = true
          → SortedList (.val k)
          → SortedList lo

-- Now define insert for SortedList that maintains the ordering.
def SortedList.insert (k : N)
    (p : Bound.ble lo (.val k) = true)
    : SortedList lo → SortedList lo
  | .snil => .scons k p .snil
  | .scons k' q rest =>
    match h : N.ble k k' with
    | true  =>
      -- k ≤ k': insert k here, before k'
      -- h : N.ble k k' = true is the bound proof for k'
      sorry
    | false =>
      -- k > k': keep k', insert k deeper
      -- ble_false_rev h : N.ble k' k = true
      sorry

def BSTM.search (k : N) : BSTM lo hi mem → Bool
  | .leaf => sorry
  | .node k' _ _ left right =>
    if N.ble k k' then
      if N.ble k' k then true
      else sorry
    else sorry

end Lec20
