/-
  Lecture 21: Huffman Coding — A Verified Case Study
  Companion Lean 4 file

  We use Lean's standard library (Nat, List, Option) from now on.
  These are the same inductive types we built in Lectures 19–20,
  but the library provides additional automation.
-/

namespace Lec21

/-! ## Part I: Basic Definitions -/

/-- A single bit: left (O) or right (I) in the code tree. -/
inductive Bit : Type where
  | O : Bit
  | I : Bit
deriving DecidableEq, Repr, BEq

/-- A Huffman tree: symbols at leaves, pure branching at internal nodes. -/
inductive HTree : Type where
  | leaf (sym : Nat) : HTree
  | node (left right : HTree) : HTree
deriving Repr

open Bit HTree

/-! ## Part II: Encoding -/

/-- Encode a single symbol: find its root-to-leaf path.
    Returns `none` if the symbol is not in the tree. -/
def encodeSym : HTree → Nat → Option (List Bit)
  | .leaf s,   n =>
      if n = s then some [] else none
  | .node l r, n =>
      match encodeSym l n with
      | some bs => some (.O :: bs)
      | none    =>
        match encodeSym r n with
        | some bs => some (.I :: bs)
        | none    => none

/-- Encode a list of symbols by concatenating their individual codes.
    Returns `none` if any symbol is missing from the tree. -/
def encodeMsg : HTree → List Nat → Option (List Bit)
  | _, []      => some []
  | t, n :: ns =>
      match encodeSym t n with
      | none    => none
      | some bs =>
        match encodeMsg t ns with
        | none      => none
        | some rest => some (bs ++ rest)


/-! ## Part III: Decoding -/

/-- Decode one symbol: walk the tree following bits until a leaf.
    Returns the symbol and the remaining (unconsumed) bits. -/
def decodeOne : HTree → List Bit → Option (Nat × List Bit)
  | .leaf s,   bs       => some (s, bs)
  | .node _ _, []       => none
  | .node l _, .O :: bs => decodeOne l bs
  | .node _ r, .I :: bs => decodeOne r bs

/-- Decode exactly `k` symbols from a bit stream. -/
def decodeMsg : HTree → Nat → List Bit → Option (List Nat)
  | _, 0,     _  => some []
  | t, k + 1, bs =>
      match decodeOne t bs with
      | none           => none
      | some (n, rest) =>
        match decodeMsg t k rest with
        | none    => none
        | some ns => some (n :: ns)


/-! ## Examples -/

/-- An example tree:
        node
       /    \
    leaf 0   node
            /    \
         leaf 1  leaf 2

    Codes: 0 → [O],  1 → [I,O],  2 → [I,I]
-/
def exTree : HTree :=
  .node (.leaf 0)
        (.node (.leaf 1) (.leaf 2))

-- Check encoding
#eval encodeSym exTree 0     -- some [Bit.O]
#eval encodeSym exTree 1     -- some [Bit.I, Bit.O]
#eval encodeSym exTree 2     -- some [Bit.I, Bit.I]
#eval encodeSym exTree 99    -- none

#eval encodeMsg exTree [0, 1, 2]
-- some [Bit.O, Bit.I, Bit.O, Bit.I, Bit.I]

-- Check decoding
#eval decodeOne exTree [O, I, O, I, I]
-- some (0, [Bit.I, Bit.O, Bit.I, Bit.I])

#eval decodeMsg exTree 3 [O, I, O, I, I]
-- some [0, 1, 2]


/-! ## Part IV: Verification -/

/-! ### The key lemma

If encoding symbol `n` in tree `t` produces bits `bs`, then
`decodeOne t (bs ++ rest)` recovers `n` and leaves `rest` untouched.

This is the operational content of prefix-freeness: the decoder
consumes exactly the bits for one symbol and no more. -/

theorem decodeOne_encodeSym (t : HTree) (n : Nat) (bs rest : List Bit)
    (h : encodeSym t n = some bs) :
    decodeOne t (bs ++ rest) = some (n, rest) := by
  induction t generalizing bs with
  | leaf s =>
    -- h : (if n = s then some [] else none) = some bs
    simp only [encodeSym] at h
    split at h
    · -- n = s: h says some [] = some bs, so bs = []
      simp_all [decodeOne]
    · -- n ≠ s: h says none = some bs — contradiction
      contradiction
  | node l r ih_l ih_r =>
    -- h : (match encodeSym l n with ...) = some bs
    simp only [encodeSym] at h
    -- Case split on whether n is in the left subtree
    split at h
    ·
      -- encodeSym l n = some bs_l, so bs = O :: bs_l
      next x bs_l h_l =>
        -- h : some (O :: bs_l) = some bs
        simp only [Option.some.injEq] at h; subst h
        -- goal: decodeOne (.node l r) ((O :: bs_l) ++ rest) = some (n, rest)
        -- ι-step: reduces to decodeOne l (bs_l ++ rest)
        simp only [List.cons_append]
        simp only [decodeOne]
        exact ih_l bs_l h_l
    · -- encodeSym l n = none, try right subtree
      split at h
      · -- encodeSym r n = some bs_r, so bs = I :: bs_r
        next bs_r h_r =>
          simp only [Option.some.injEq] at h; subst h
          simp only [List.cons_append]
          simp only [decodeOne]
          exact ih_r bs_r h_r
      · -- both none: h says none = some bs — contradiction
        contradiction


/-! ### The roundtrip theorem

If encoding succeeds, decoding recovers the original message. -/

theorem roundtrip (t : HTree) (ns : List Nat) (bs : List Bit)
    (h : encodeMsg t ns = some bs) :
    decodeMsg t ns.length bs = some ns := by
  induction ns generalizing bs with
  | nil =>
    -- h : some [] = some bs
    simp [encodeMsg] at h; subst h
    -- goal: decodeMsg t 0 [] = some []
    rfl
  | cons n ns ih =>
    -- h : encodeMsg t (n :: ns) = some bs
    -- Unfold one step to expose the matches
    simp only [encodeMsg] at h
    -- Case split on encodeSym t n
    split at h
    · contradiction  -- encodeSym t n = none
    · next bs1 h_enc1 =>
      -- encodeSym t n = some bs1
      -- Now case split on encodeMsg t ns
      split at h
      · contradiction  -- encodeMsg t ns = none
      · next bs2 h_enc2 =>
        -- encodeMsg t ns = some bs2
        -- h : some (bs1 ++ bs2) = some bs, so bs = bs1 ++ bs2
        simp only [Option.some.injEq] at h; subst h
        -- goal: decodeMsg t (n :: ns).length (bs1 ++ bs2)
        --       = some (n :: ns)
        simp only [List.length_cons, decodeMsg]
        -- Rewrite decodeOne using the key lemma
        rw [decodeOne_encodeSym t n bs1 bs2 h_enc1]
        -- The match on `some (n, bs2)` fires:
        simp only
        -- Now the goal involves decodeMsg t ns.length bs2
        -- Apply the induction hypothesis
        rw [ih bs2 h_enc2]


/-! ## Part V: Building the Tree -/

/-- Insert a weighted tree into a list sorted by weight. -/
def insertSorted : (Nat × HTree) → List (Nat × HTree) → List (Nat × HTree)
  | x, []      => [x]
  | x, y :: ys =>
      if x.1 <= y.1
      then x :: y :: ys
      else y :: insertSorted x ys

/-- insertSorted preserves list length (adds exactly one element). -/
theorem length_insertSorted (x : Nat × HTree) (ys : List (Nat × HTree)) :
    (insertSorted x ys).length = ys.length + 1 := by
  induction ys with
  | nil => simp [insertSorted]
  | cons y ys ih =>
    simp only [insertSorted]
    split
    · simp
    · simp [ih]

/-- Build a Huffman tree by repeatedly merging the two lightest trees. -/
def buildTree : List (Nat × HTree) → Option HTree
  | []  => none
  | [(_, t)] => some t
  | (w1, t1) :: (w2, t2) :: rest =>
      buildTree (insertSorted (w1 + w2, .node t1 t2) rest)
termination_by l => l.length
decreasing_by
  simp [length_insertSorted]

/-- Build the initial priority queue from (symbol, frequency) pairs. -/
def freqsToQueue : List (Nat × Nat) → List (Nat × HTree)
  | [] => []
  | (sym, freq) :: rest =>
      insertSorted (freq, .leaf sym) (freqsToQueue rest)

/-- The complete Huffman algorithm: from frequencies to a code tree. -/
def huffman (freqs : List (Nat × Nat)) : Option HTree :=
  buildTree (freqsToQueue freqs)

-- Example: build a tree from frequencies
#eval huffman [(0, 3), (1, 2), (2, 1)]

-- End-to-end example
#eval do
  let t ← huffman [(0, 3), (1, 2), (2, 1)]
  let bs ← encodeMsg t [0, 0, 1, 2, 0]
  let ns ← decodeMsg t 5 bs
  return ns
-- Expected: some [0, 0, 1, 2, 0]

end Lec21
