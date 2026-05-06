/-
  Lecture 23: Well-Founded Recursion and Proof Automation
  Companion Lean file
-/


namespace Lec23

-- ============================================================
-- Part I: Structural vs Well-Founded Recursion
-- ============================================================

-- Structural recursion: recursive call on a subterm.
def length' : List α → Nat
  | []     => 0
  | _ :: t => 1 + length' t

#eval length' [1, 2, 3]   -- 3

-- Well-founded recursion: GCD by the Euclidean algorithm.
-- We need dependent if (if h : ...) so that h : m ≠ 0 is available
-- for the termination proof. The default tactic cannot prove n % m < m
-- on its own because % is outside omega's fragment.
def gcd (m n : Nat) : Nat :=
  if h : m = 0 then n
  else gcd (n % m) m
termination_by m
decreasing_by exact Nat.mod_lt n (Nat.pos_of_ne_zero h)

#eval gcd 12 8    -- 4
#eval gcd 100 37  -- 1
#eval gcd 0 5     -- 5

-- Division by repeated subtraction.
-- n - k < n whenever k > 0 and n ≥ k.
def div' (n k : Nat) : Nat :=
  if k = 0 then 0
  else if n < k then 0
  else 1 + div' (n - k) k
termination_by n

#eval div' 10 3    -- 3
#eval div' 7 2     -- 3


-- ============================================================
-- The Ackermann function: lexicographic order
-- ============================================================

-- Named parameters so termination_by can reference them.
def ack (n m : Nat) : Nat :=
  match n, m with
  | 0,     m     => m + 1
  | n + 1, 0     => ack n 1
  | n + 1, m + 1 => ack n (ack (n + 1) m)
termination_by (n, m)

-- Checking the three cases:
-- Case 2: ack (n+1) 0 → ack n 1.       Measure: (n,1) < (n+1,0) because n < n+1.  ✓
-- Case 3 inner: ack (n+1) (m+1) → ack (n+1) m.  Same first component, m < m+1.     ✓
-- Case 3 outer: ack (n+1) (m+1) → ack n (ack (n+1) m).  n < n+1, second irrelevant. ✓

#eval ack 0 0     -- 1
#eval ack 1 1     -- 3
#eval ack 2 2     -- 7
#eval ack 3 3     -- 61


-- ============================================================
-- Part II: The Theory
-- ============================================================

-- Acc.inv: if x is accessible and y < x, then y is accessible.
-- Pattern-matches on the Acc constructor to extract the inner proof.
def Acc.inv' {r : α → α → Prop} {x y : α}
    (hacc : Acc r x) (hr : r y x) : Acc r y :=
  match hacc with
  | .intro _ h => h y hr

-- Proving < is well-founded on Nat by induction.
-- We write (n : Nat) explicitly so Lean resolves the < instance.
theorem nat_lt_wf (n : Nat) : Acc (· < ·) n := by
  induction n with
  | zero =>
    exact Acc.intro 0 (fun _ hm => absurd hm (Nat.not_lt_zero _))
  | succ n ih =>
    exact Acc.intro (n + 1) (fun m hm => by
      have : m = n ∨ m < n := by omega
      cases this with
      | inl h => subst h; exact ih
      | inr h => exact ih.inv h)

-- GCD with explicit decreasing_by proof.
-- Note: `if h : m = 0` (dependent if) gives us h : ¬(m = 0) in the else branch.
def gcd' (m n : Nat) : Nat :=
  if _ : m = 0 then n
  else gcd' (n % m) m
termination_by m
decreasing_by
  rename_i h
  refine Nat.mod_lt n ?_
  exact Nat.zero_lt_of_ne_zero h


-- ============================================================
-- Part III: Proof Automation — simp
-- ============================================================

-- simp: repeatedly applies rewrite rules left-to-right.
example : 0 + n + 0 = n := by simp

-- Registering your own simp lemmas
def double (n : Nat) := n + n

@[simp] theorem double_zero : double 0 = 0 := by rfl
@[simp] theorem double_succ (n : Nat) :
    double (n + 1) = double n + 2 := by
  unfold double; omega

-- simp [double] unfolds the definition of double as a rewrite rule
example : double 3 = 6 := by simp [double]

-- simp with hypotheses: uses h as a rewrite rule
example (h : x = 0) : x + x = 0 := by simp [h]

-- simp at h: simplifies a hypothesis
example (h : x + 0 = y) : x = y := by
  simp at h   -- h becomes h : x = y
  exact h


-- ============================================================
-- Part III: Proof Automation — omega
-- ============================================================

-- omega: decision procedure for linear arithmetic over Nat and Int.
example : ∀ n : Nat, 0 ≤ n := by omega
example (h : n < m) : n + 1 ≤ m := by omega
example (h : a + b = 10) (h2 : a ≤ 3) : b ≥ 7 := by omega


-- ============================================================
-- Part III: Proof Automation — decide
-- ============================================================

example : 10 * 20 = 200 := by decide
example : ¬(3 < 2 ∧ True) := by decide
example : 37 * 41 = 1517 := by decide


-- ============================================================
-- Part IV: Combining the Tools
-- ============================================================

-- Merge: named parameters so termination_by can reference them.
def merge' [Ord α] (as bs : List α) : List α :=
  match as, bs with
  | [],    bs    => bs
  | as,    []    => as
  | a::as, b::bs =>
    if Ordering.isLE (Ord.compare a b) --|>.isLE
    then a :: merge' as (b::bs)
    else b :: merge' (a::as) bs
termination_by as.length + bs.length

#eval merge' [1, 3, 5] [2, 4, 6]    -- [1, 2, 3, 4, 5, 6]

-- 0 + n = n needs induction because Lean defines + by recursion on
-- the second argument: n + 0 reduces, but 0 + n does not.

-- Step by step:
theorem zero_add_manual : ∀ n, 0 + n = n := by
  intro n; induction n with
  | zero => rfl
  | succ n ih => rw [Nat.add_succ, ih]

-- With omega (one step):
theorem zero_add_auto : ∀ n, 0 + n = n := by
  intro n; omega

-- omega handles addition commutativity:
theorem add_comm' (n m : Nat) : n + m = m + n := by omega

-- But NOT multiplication commutativity (nonlinear):
theorem mul_comm' (n m : Nat) : n * m = m * n := by
  induction n with
  | zero => simp
  | succ n ih => simp [Nat.succ_mul, Nat.mul_succ, ih]


-- ============================================================
-- Part V: Under the Hood
-- ============================================================

-- The elaborator rewrites well-founded recursion as structural
-- recursion on a shadow Acc argument. See slides for details.

-- Large elimination: Acc lives in Prop but gcd returns Nat.
-- CIC allows this because Acc has one constructor and no new
-- data in Type (x is an index, h is in Prop).

-- This is ILLEGAL (would extract data from a proof):
-- def bad (h : ∃ n : Nat, n > 5) : Nat :=
--   match h with | ⟨w, _⟩ => w


-- ============================================================
-- Exercises
-- ============================================================

-- Exercise 1: log2
def log2 (n : Nat) : Nat :=
  if n ≤ 1 then 0
  else 1 + log2 (n / 2)
termination_by n

#eval log2 1     -- 0
#eval log2 2     -- 1
#eval log2 8     -- 3
#eval log2 1024  -- 10


-- Exercise 2: Collatz
-- Cannot be defined as a total function — termination is unproven!
partial def collatzSteps : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n => if n % 2 = 0
         then 1 + collatzSteps (n / 2)
         else 1 + collatzSteps (3 * n + 1)

#eval collatzSteps 27    -- 111


-- Exercise 3: commutativity via omega
theorem nat_add_comm (n m : Nat) : n + m = m + n := by omega


-- Exercise 4: Fibonacci via well-founded recursion
def fib : Nat → Nat
  | 0     => 0
  | 1     => 1
  | n + 2 => fib (n + 1) + fib n

def fib' (n : Nat) : Nat :=
  if n = 0 then 0
  else if n = 1 then 1
  else fib' (n - 1) + fib' (n - 2)
termination_by n

#eval fib 10     -- 55
#eval fib' 10    -- 55


-- Exercise 5: simp lemmas for List.length + map
@[simp] theorem length_map' (f : α → β) (xs : List α) :
    (xs.map f).length = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

def squares (xs : List Nat) : List Nat := xs.map (fun x => x * x)

example : (squares [1,2,3]).length = 3 := by simp [squares]


-- Exercise 6 (Harder): buildTree termination from Lecture 21


-- Exercise 7: Integer square root
def isqrt (n : Nat) : Nat :=
  isqrtAux n n
where
  isqrtAux (n k : Nat) : Nat :=
    if k = 0 then 0
    else if k * k ≤ n then k
    else isqrtAux n (k - 1)
  termination_by k


#eval isqrt 0     -- 0
#eval isqrt 1     -- 1
#eval isqrt 4     -- 2
#eval isqrt 9     -- 3
#eval isqrt 100   -- 10

end Lec23
