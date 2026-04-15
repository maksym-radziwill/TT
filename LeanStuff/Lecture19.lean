/-
  Lecture 19: Verified Functional Programming in Lean 4
  Standalone file — every definition and proof from the lecture.
  Open in VS Code with the Lean 4 extension to typecheck.
-/

namespace Lec

-- ════════════════════════════════════════════════════════════
-- Part I: Booleans
-- ════════════════════════════════════════════════════════════

inductive Bool : Type where
  | true  : Bool
  | false : Bool

def not : Bool → Bool
  | .true  => .false
  | .false => .true

def and : Bool → Bool → Bool
  | .true,  b => b
  | .false, _ => .false

def or : Bool → Bool → Bool
  | .true,  _ => .true
  | .false, b => b

-- Computation
#reduce not .true            -- Bool.false
#reduce and .true .false     -- Bool.false
#reduce or .false .true      -- Bool.true

-- Theorems

theorem not_not (b : Bool) : not (not b) = b := by
  cases b
  · rfl
  · rfl

theorem not_not' (b : Bool) : not (not b) = b :=
  match b with
  | .true  => rfl
  | .false => rfl

theorem and_comm (a b : Bool) : and a b = and b a := by
  cases a <;> cases b <;> rfl

-- Exercises (uncomment and fill in)
-- theorem or_comm (a b : Bool) : or a b = or b a := by sorry
-- theorem and_assoc (a b c : Bool) : and (and a b) c = and a (and b c) := by sorry

-- ════════════════════════════════════════════════════════════
-- Part II: Natural Numbers
-- ════════════════════════════════════════════════════════════

inductive N : Type where
  | zero : N
  | succ : N → N

def add : N → N → N
  | m, .zero   => m
  | m, .succ k => .succ (add m k)

-- Computation
#reduce add (.succ .zero) (.succ (.succ .zero))
-- N.succ (N.succ (N.succ N.zero))    i.e. 1 + 2 = 3

-- A definitional equality: rfl suffices
theorem add_zero (m : N) : add m .zero = m :=
  rfl

-- A propositional equality: induction required
theorem zero_add (m : N) : add .zero m = m := by
  induction m with
  | zero      => rfl
  | succ k ih =>
    -- goal: add .zero (.succ k) = .succ k
    -- second arg is .succ k (a constructor), so ι fires:
    -- add .zero (.succ k) reduces to .succ (add .zero k)
    show N.succ (add .zero k) = N.succ k
    rw [ih]

-- Definitional: ι fires on .succ k
theorem add_succ (m k : N) : add m (.succ k) = .succ (add m k) :=
  rfl

-- Propositional: need induction
theorem succ_add (m k : N) : add (.succ m) k = .succ (add m k) := by
  induction k with
  | zero      => rfl
  | succ k ih =>
    show N.succ (add (.succ m) k) = N.succ (N.succ (add m k))
    rw [ih]

-- Commutativity
theorem add_comm (m n : N) : add m n = add n m := by
  induction n with
  | zero      => rw [add_zero, zero_add]
  | succ k ih => rw [add_succ, succ_add, ih]

-- Associativity
theorem add_assoc (m n k : N) : add (add m n) k = add m (add n k) := by
  induction k with
  | zero      => rfl
  | succ k ih =>
    show N.succ (add (add m n) k) = N.succ (add m (add n k))
    rw [ih]

-- Multiplication
def mul : N → N → N
  | _, .zero   => .zero
  | m, .succ k => add (mul m k) m

#reduce mul (.succ (.succ .zero)) (.succ (.succ (.succ .zero)))
-- six succs: 2 × 3 = 6

theorem mul_zero (m : N) : mul m .zero = .zero :=
  rfl

theorem zero_mul (m : N) : mul .zero m = .zero := by
  induction m with
  | zero      => rfl
  | succ k ih =>
    show add (mul .zero k) .zero = .zero
    rw [add_zero, ih]

-- ════════════════════════════════════════════════════════════
-- Part III: Lists
-- ════════════════════════════════════════════════════════════

inductive List (A : Type) : Type where
  | nil  : List A
  | cons : A → List A → List A

def length : List A → N
  | .nil       => .zero
  | .cons _ xs => .succ (length xs)

#reduce length (.cons 1 (.cons 2 (.cons 3 (.nil : List Nat))))
-- N.succ (N.succ (N.succ N.zero))

def append : List A → List A → List A
  | .nil,       ys => ys
  | .cons x xs, ys => .cons x (append xs ys)

-- Definitional
theorem append_nil (ys : List A) : append .nil ys = ys :=
  rfl

-- Propositional: induction required
theorem nil_append (xs : List A) : append xs .nil = xs := by
  induction xs with
  | nil         => rfl
  | cons x xs ih =>
    show List.cons x (append xs .nil) = List.cons x xs
    rw [ih]

-- Length distributes over append
theorem length_append (xs ys : List A)
    : length (append xs ys) = add (length xs) (length ys) := by
  induction xs with
  | nil =>
    -- goal: length (append .nil ys) = add (length .nil) (length ys)
    simp only [append]
    -- unfolds append .nil ys to ys:
    --        length ys = add (length .nil) (length ys)
    simp only [length]
    -- unfolds length .nil to .zero:
    --        length ys = add .zero (length ys)
    rw [zero_add]
  | cons x xs ih =>
    -- goal: length (append (.cons x xs) ys)
    --     = add (length (.cons x xs)) (length ys)
    simp only [append]
    -- unfolds append (.cons x xs) ys to .cons x (append xs ys)
    simp only [length]
    -- unfolds both length calls:
    --   .succ (length (append xs ys))
    --     = add (.succ (length xs)) (length ys)
    rw [succ_add, ih]

-- Associativity
theorem append_assoc (xs ys zs : List A)
    : append (append xs ys) zs = append xs (append ys zs) := by
  induction xs with
  | nil         => rfl
  | cons x xs ih =>
    show List.cons x (append (append xs ys) zs)
       = List.cons x (append xs (append ys zs))
    rw [ih]

-- Reverse
def rev : List A → List A
  | .nil       => .nil
  | .cons x xs => append (rev xs) (.cons x .nil)

-- Key lemma: rev distributes over append
theorem rev_append (xs ys : List A)
    : rev (append xs ys) = append (rev ys) (rev xs) := by
  induction xs with
  | nil =>
    -- goal: rev (append .nil ys) = append (rev ys) (rev .nil)
    simp only [append, rev]
    -- goal: rev ys = append (rev ys) .nil
    rw [nil_append]
  | cons x xs ih =>
    -- unfold append and rev to expose structure
    simp only [append, rev]
    rw [ih, append_assoc]

-- Reverse is an involution
theorem rev_rev (xs : List A) : rev (rev xs) = xs := by
  induction xs with
  | nil         => rfl
  | cons x xs ih =>
    simp only [rev]
    rw [rev_append]
    simp only [rev, append]
    rw [ih]

end Lec
