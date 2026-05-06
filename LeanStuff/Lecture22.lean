/-
  Lecture 22: Structures and Type Classes
  Companion Lean file
-/

-- ============================================================
-- Part I: Structures
-- ============================================================

-- Declaring a structure
structure Point (α : Type) where
  x : α
  y : α
deriving Repr

-- What Lean generates: check for yourself
#check @Point.mk    -- {α : Type} → α → α → Point α
#check @Point.x     -- {α : Type} → Point α → α
#check @Point.y     -- {α : Type} → Point α → α
#print Point
-- structure Point (α : Type) : Type
-- fields:
--   Point.x : α
--   Point.y : α
-- constructor:
--   Point.mk {α : Type} (x y : α) : Point α

-- Compare with the hand-written equivalent:
inductive Point' (α : Type) where
  | mk : α → α → Point' α
def Point'.x : Point' α → α | .mk a _ => a
def Point'.y : Point' α → α | .mk _ b => b

-- Building structures
def p1 := Point.mk 10 20
def p2 : Point Nat := ⟨10, 20⟩
def p3 : Point Nat := { x := 10, y := 20 }
def p4 : Point Nat := { y := 20, x := 10 }

-- Dot notation
def p : Point Nat := { x := 10, y := 20 }
#eval p.x         -- 10
#eval p.y         -- 20

def Point.add (p q : Point Nat) : Point Nat :=
  { x := p.x + q.x, y := p.y + q.y }

def q : Point Nat := { x := 3, y := 4 }
#eval p.add q     -- { x := 13, y := 24 }

-- Record update
-- (we shadow p here; in a real file you might use a different name)
namespace RecordUpdate
  def p : Point Nat := { x := 1, y := 2 }
  #eval { p with y := 3 }    -- { x := 1, y := 3 }
  #eval { p with x := 4 }    -- { x := 4, y := 2 }
end RecordUpdate

-- Structure inheritance
inductive Color where | red | green | blue
deriving Repr

structure ColorPoint (α : Type) extends Point α where
  c : Color
deriving Repr

def cp : ColorPoint Nat :=
  { x := 1, y := 2, c := .red }
#eval cp.x          -- 1
#eval cp.toPoint     -- { x := 1, y := 2 }

def cp2 : ColorPoint Nat :=
  { RecordUpdate.p with c := .blue }

-- Multiple inheritance
structure RGBValue where
  red : Nat
  green : Nat
  blue : Nat

structure RedGreenPoint (α : Type)
    extends Point α, RGBValue where
  no_blue : blue = 0

-- ============================================================
-- Part II: From Structures to Classes
-- ============================================================

-- First attempt: pass the implementation as a structure
namespace ManualApproach
  structure Add' (α : Type) where
    add : α → α → α

  def double' (s : Add' α) (x : α) : α :=
    s.add x x

  #eval double' { add := Nat.add } 10     -- 20
  #eval double' { add := Int.add } 10     -- 20
end ManualApproach

-- The key idea: replace structure with class
namespace Lec22

class Add (α : Type) where
  add : α → α → α

-- Compare the two versions of double:
-- with structure: caller must pass the record
-- def double' (s : Add' α) (x : α) : α := s.add x x
-- with class: Lean finds the record automatically
def double [Add α] (x : α) : α := Add.add x x

-- Declaring instances
instance : Add Nat where
  add := Nat.add

instance : Add Int where
  add := Int.add

instance : Add Float where
  add := Float.add

-- Using instance-implicit arguments
#eval double 10           -- 20
#eval double (10 : Int)    -- 20
#eval double (7 : Float)   -- 14.0

-- Chaining instances
instance [Add α] [Add β] : Add (α × β) where
  add p q := (Add.add p.1 q.1, Add.add p.2 q.2)

#eval double (3, 5)        -- (6, 10)
#eval double ((1, 2), 3)   -- ((2, 4), 6)

end Lec22

-- ============================================================
-- Part III: Key Library Classes
-- ============================================================

-- How notation works:
-- infixl:65 " + " => HAdd.hAdd
-- (this is already defined in the standard library)

-- OfNat: polymorphic numeric literals
-- (the class itself is in the standard library; here we show a custom instance)

structure Rational where
  num : Int
  den : Nat
  inv : den ≠ 0
deriving Repr

instance : OfNat Rational n where
  ofNat := { num := n, den := 1, inv := by decide }

instance : ToString Rational where
  toString r := s!"{r.num}/{r.den}"

#eval (2 : Rational)    -- 2/1
#check (2 : Rational)   -- 2 : Rational
#check (2 : Nat)         -- 2 : Nat

-- Inhabited: default elements
-- (the class is in the standard library; here we demonstrate chaining)
#eval (default : Nat × Bool)   -- (0, false)  [stdlib: Inhabited Bool has default := false]

-- ToString: custom instance
structure Person where
  name : String
  age  : Nat

instance : ToString Person where
  toString p := p.name ++ "@" ++ toString p.age

#eval toString { name := "Leo", age := 542 : Person }
-- "Leo@542"

-- ============================================================
-- Part IV: Decidable Propositions
-- ============================================================

-- The Decidable class is in the standard library:
   class inductive Decidable2 (p : Prop) where
     | isFalse (h : ¬p) : Decidable2 p
     | isTrue  (h : p)  : Decidable2 p
-- Note: Decidable p : Type, not Prop.

-- How if works (already defined in the standard library):
   def ite2 (c : Prop) [h : Decidable2 c] (t e : α) : α :=
     match h with
     | .isTrue  _ => t
     | .isFalse _ => e

-- DecidableEq and deriving
inductive Bit : Type where
  | O : Bit
  | I : Bit
deriving DecidableEq, Repr

-- Decidability composes:
-- The standard library provides instances like:
--   instance [Decidable p] [Decidable q] : Decidable (p ∧ q) := ...
--   instance [Decidable p] [Decidable q] : Decidable (p ∨ q) := ...
--   instance [Decidable p] : Decidable (¬p) := ...

-- This lets us write compound conditions:
def step (a b x : Nat) : Nat :=
  if x < a ∨ x > b then 0 else 1

#eval step 3 7 5    -- 1
#eval step 3 7 1    -- 0

-- The decide tactic
example : 10 < 5 ∨ 1 > 0 := by decide
example : ¬(True ∧ False) := by decide
example : 10 * 20 = 200   := by decide

-- ============================================================
-- Part V: Coercions and Scope
-- ============================================================

-- Coercions via type classes (Coe Nat Int is in the standard library)
-- instance : Coe Nat Int where
--   coe := Int.ofNat

-- Local instances
section
local instance : Add (Point Nat) where
  add a b := { x := a.x + b.x, y := a.y + b.y }
def doublePoint (p : Point Nat) := p + p
#eval doublePoint { x := 1, y := 2 }  -- { x := 2, y := 4 }
end
-- Add (Point Nat) is no longer active here

-- Scoped instances
namespace PointOps
scoped instance : Add (Point Nat) where
  add a b := { x := a.x + b.x, y := a.y + b.y }
end PointOps
-- not active outside; use `open PointOps` to activate

-- ============================================================
-- Part VI: A Complete Example
-- ============================================================

inductive Parity : Type where
  | even : Parity
  | odd  : Parity
deriving Repr

instance : Add Parity where
  add
    | .even, p     => p
    | .odd,  .even => .odd
    | .odd,  .odd  => .even

instance : ToString Parity where
  toString | .even => "EVEN" | .odd => "odd"

instance : OfNat Parity 0 where ofNat := .even
instance : OfNat Parity 1 where ofNat := .odd

instance : BEq Parity where
  beq a b := match a, b with
    | .even, .even | .odd, .odd => true
    | _, _ => false

-- double using the standard library's Add (not Lec22.Add)
def double [Add α] (x : α) : α := x + x

#eval double (1 : Parity)          -- even (odd + odd)
#eval 1 + (Parity.odd)  -- odd
#eval (0 : Parity)
