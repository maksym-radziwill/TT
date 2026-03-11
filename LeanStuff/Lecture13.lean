/-
  Lecture 13 — Monads in Practice
  Companion Lean 4 code

  This file contains working versions of every Lean example
  from the slides.  You can step through it in VS Code or
  the Lean web editor.
-/

-- ============================================================
-- Part I: What Is a Monad?
-- ============================================================

/-
  The Monad interface in Lean comes from several classes:

    class Pure (m : Type → Type) where
      pure : α → m α

    class Bind (m : Type → Type) where
      bind : m α → (α → m β) → m β

    class Monad (m : Type → Type) extends Applicative m, Bind m

  An **instance** is a concrete implementation of `pure` and `bind`
  for a specific type constructor.  The compiler passes the instance
  implicitly wherever a `[Monad m]` constraint appears.

  Type classes are not part of System Fω — they are structures
  (record types) whose fields are functions, and instances are
  terms inhabiting those structures.
-/


-- ============================================================
-- Part II: The Option Monad
-- ============================================================

/-
  Lean's `Option` is defined as:

    inductive Option (α : Type) where
      | none : Option α
      | some : α → Option α

  The built-in Monad instance is essentially:

    instance : Monad Option where
      pure x := some x
      bind
        | none,     _ => none
        | some x,   f => f x

  Let's see it in action.
-/

section OptionExamples

-- Simulated lookup functions
structure Student where
  name     : String
  courseId : Nat
  deriving Repr

structure Course where
  cid   : Nat
  title : String
  deriving Repr

def students : List (String × Student) :=
  [("Alice", ⟨"Alice", 101⟩), ("Charlie", ⟨"Charlie", 102⟩)]

def courses : List (Nat × Course) :=
  [(101, ⟨101, "CS Foundations"⟩), (102, ⟨102, "Algebra"⟩)]

def grades : List (Nat × Nat) :=   -- keyed by course id
  [(101, 85), (102, 92)]

def lookupStudent (name : String) : Option Student :=
  (students.find? fun (n, _) => n == name).map Prod.snd

def lookupCourse (s : Student) : Option Course :=
  (courses.find? fun (id, _) => id == s.courseId).map Prod.snd

def lookupGrade (c : Course) : Option Nat :=
  (grades.find? fun (id, _) => id == c.cid).map Prod.snd

-- Chaining with >>= (bind)
def getGrade_bind (name : String) : Option Nat :=
  lookupStudent name >>= fun s =>
  lookupCourse s     >>= fun c =>
  lookupGrade c

-- The same thing with do-notation
def getGrade (name : String) : Option Nat := do
  let student ← lookupStudent name
  let course  ← lookupCourse student
  lookupGrade course

-- Success path
#eval getGrade "Alice"     -- some 85

-- Failure propagation
#eval getGrade "Bob"       -- none  (student not found)

end OptionExamples


-- ============================================================
-- Part III: The List Monad
-- ============================================================

/-
  Lean 4 provides `Pure` and `Bind` for `List` but does not bundle
  them into a `Monad` instance in the standard library.  We provide
  one here so that `do`-notation works with lists.
-/

instance : Monad List where
  pure x := [x]
  bind xs f := xs.flatMap f

section ListExamples

-- Cartesian product via the list monad
def pairs : List (Nat × Char) := do
  let x ← [1, 2, 3]
  let y ← ['a', 'b']
  pure (x, y)

#eval pairs
-- [(1, 'a'), (1, 'b'), (2, 'a'), (2, 'b'), (3, 'a'), (3, 'b')]

-- Pythagorean triples
def triples (n : Nat) : List (Nat × Nat × Nat) := do
  let a ← List.range' 1 n
  let b ← List.range' a (n + 1 - a)
  let c ← List.range' b (n + 1 - b)
  if a * a + b * b == c * c then
    pure (a, b, c)
  else
    []   -- empty list = prune this branch

#eval triples 20
-- [(3, 4, 5), (5, 12, 13), (6, 8, 10), (8, 15, 17), (9, 12, 15)]

-- Nondeterministic choice
def coinFlip : List String := ["heads", "tails"]

def twoFlips : List (String × String) := do
  let first  ← coinFlip
  let second ← coinFlip
  pure (first, second)

#eval twoFlips
-- [("heads","heads"), ("heads","tails"), ("tails","heads"), ("tails","tails")]

end ListExamples


-- ============================================================
-- Part IV: The State Monad
-- ============================================================

/-
  In Lean, the state monad is defined via StateT:

    def StateT (σ : Type) (m : Type → Type) (α : Type) :=
      σ → m (α × σ)

    abbrev StateM (σ : Type) := StateT σ Id
    -- so StateM σ α  =  σ → α × σ

  The instance threads state through bind:

    instance : Monad (StateM σ) where
      pure a   := fun s => (a, s)
      bind m f := fun s => let (a, s') := m s; f a s'
-/

section StateExamples

-- Increment a counter
def incr : StateM Nat Unit :=
  modify fun x => x + 1

def threeIncrements : StateM Nat Unit := do
  incr; incr; incr

#eval threeIncrements.run 0    -- ((), 3)
#eval threeIncrements.run 10   -- ((), 13)

-- Fibonacci via state monad
def fib (n : Nat) : Nat :=
  let loop : StateM (Nat × Nat) Nat := do
    for _ in [:n] do
      let (a, b) ← get
      set (b, a + b)
    let (a, _) ← get
    pure a
  (loop.run (0, 1)).1

#eval fib 0    -- 0
#eval fib 1    -- 1
#eval fib 5    -- 5
#eval fib 10   -- 55

-- Summing a list with state
def sumList (xs : List Nat) : Nat :=
  let go : StateM Nat Unit := do
    for x in xs do
      modify (· + x)
  (go.run 0).2

#eval sumList [1, 2, 3, 4, 5]   -- 15

-- Tracing the bind manually:
-- `get >>= fun s => set (s + 1)` with initial state 5
-- Step 1: get 5 = (5, 5)         — result is 5, state unchanged
-- Step 2: set 6 5 = ((), 6)      — result is (), state becomes 6
-- Final: ((), 6)
#eval (get >>= fun s => set (s + 1) : StateM Nat Unit).run 5
-- ((), 6)

end StateExamples


-- ============================================================
-- Part V: The IO Monad
-- ============================================================

/-
  IO α is an opaque computation that interacts with the outside
  world and produces a value of type α.  You cannot pattern match
  on it.  The only way to combine IO actions is via `pure` and `bind`.

  The runtime executes IO by running `main`.
-/

-- A simple IO program (uncomment to use as main):
-- def main : IO Unit := do
--   IO.println "What is your name?"
--   let stdin ← IO.getStdin
--   let name ← stdin.getLine
--   IO.println s!"Hello, {name.trimRight}!"

-- IO values are first-class — you can store them in lists:
def greet : IO Unit := IO.println "Hello!"

def actions : List (IO Unit) :=
  [greet, IO.println "World", pure ()]

-- Execute a list of IO actions
def runAll : List (IO Unit) → IO Unit
  | []      => pure ()
  | a :: as => a >>= fun _ => runAll as

-- Or simply: actions.forM id


-- ============================================================
-- Part VI: Generic Monad Code
-- ============================================================

-- A function polymorphic in the monad
def mapM' [Monad m] (f : α → m β) : List α → m Unit
  | []      => pure ()
  | x :: xs => f x >>= fun _ => mapM' f xs

-- Instantiate with different monads:

-- m = Option: short-circuits on failure
def checkPositive (n : Int) : Option Int :=
  if n > 0 then some n else none

#eval mapM' checkPositive [1, 2, 3]     -- some ()
#eval mapM' checkPositive [1, -2, 3]    -- none

-- m = List: nondeterminism
def expand (n : Nat) : List Nat := [n, n * 10]

#eval ([1, 2, 3].flatMap expand)   -- [1, 10, 2, 20, 3, 30]

-- m = StateM: threading state
def accumulate (n : Nat) : StateM Nat Unit :=
  modify (· + n)

#eval (mapM' accumulate [1, 2, 3, 4] : StateM Nat Unit).run 0
-- ((), 10)


-- ============================================================
-- Bonus: the monad laws (stated as theorems)
-- ============================================================

/-
  Lean's `LawfulMonad` class captures the monad laws.
  The built-in instances for `Option`, `List`, `StateM`, etc.
  all have `LawfulMonad` proofs in Mathlib or the standard library.

  The laws are:

    pure_bind : ∀ (x : α) (f : α → m β),
                  pure x >>= f = f x

    bind_pure_comp : ∀ (f : α → β) (x : m α),
                       bind x (pure ∘ f) = f <$> x

    bind_assoc : ∀ (x : m α) (f : α → m β) (g : β → m γ),
                   x >>= f >>= g = x >>= fun a => f a >>= g

  These ensure that `pure` acts as an identity for `>>=`,
  and that `>>=` is associative — i.e. that effectful programs
  compose correctly regardless of how you group them.
-/

-- We can verify the laws by example:
section LawExamples

-- Left unit:  pure x >>= f  =  f x
#eval (pure 3 >>= fun x => some (x + 1) : Option Nat)   -- some 4
#eval (fun x => some (x + 1)) 3                          -- some 4

-- Right unit:  m >>= pure  =  m
#eval (some 42 >>= pure : Option Nat)                    -- some 42

-- Associativity: (m >>= f) >>= g  =  m >>= (fun x => f x >>= g)
def f' (x : Nat) : Option Nat := if x > 0 then some (x * 2) else none
def g' (x : Nat) : Option Nat := some (x + 100)

#eval ((some 5 >>= f') >>= g')                           -- some 110
#eval (some 5 >>= fun x => f' x >>= g')                  -- some 110

end LawExamples
