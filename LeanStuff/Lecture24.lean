/-
  Lecture 24: Axioms and Computation
  Companion Lean file
-/

namespace Lec24

-- ============================================================
-- Part II: Propositional Extensionality
-- ============================================================

-- propext is built in:
#check @propext  -- {a b : Prop} → (a ↔ b) → a = b

-- Example: (True ∧ True) = True
theorem tteq : (True ∧ True) = True :=
  propext ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, h⟩⟩

-- propext blocks #reduce but not #eval
def val : Nat := Eq.recOn (motive := fun _ _ => Nat) tteq 0
-- #reduce val   -- stuck
#eval val        -- 0


-- ============================================================
-- Part III: Function Extensionality
-- ============================================================

-- funext is a theorem, proved from Quot.sound:
#check @funext   -- {f g : (x : α) → β x} → (∀ x, f x = g x) → f = g
#print axioms funext  -- Quot.sound

-- Combining propext and funext: extensional sets
def MySet (α : Type) := α → Prop

namespace MySet

def mem (x : α) (s : MySet α) := s x


theorem ext {a b : MySet α} (h : ∀ x, a x ↔ b x) : a = b :=
  funext (fun x => propext (h x))

def inter (a b : MySet α) : MySet α := fun x => a x ∧ b x

theorem inter_comm (a b : MySet α) : inter a b = inter b a :=
  ext fun _ => ⟨fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩, fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩⟩

end MySet

-- funext blocks #reduce when used in a cast
def f' (x : Nat) := x
def g' (x : Nat) := 0 + x

theorem f_eq_g : f' = g' :=
  funext fun x => by
    unfold f'
    unfold g'
    simp
--    (Nat.zero_add x).symm

#reduce (1 + 1)
#reduce f_eq_g

def val2 : Nat := Eq.recOn (motive := fun _ _ => Nat) f_eq_g 0
-- #reduce val2   -- stuck (funext uses Quot.sound)
#eval val2        -- 0


-- ============================================================
-- Part IV: Quotient Types
-- ============================================================

-- The four built-in constants:
#check @Quot       -- {α : Sort u} → (α → α → Prop) → Sort u
#check @Quot.mk    -- (r : α → α → Prop) → α → Quot r
#check @Quot.ind   -- (∀ a, β (Quot.mk r a)) → (q : Quot r) → β q
#check @Quot.lift  -- (f : α → β) → (∀ a b, r a b → f a = f b) → Quot r → β

-- The axiom:
#check @Quot.sound -- r a b → Quot.mk r a = Quot.mk r b

-- Example: integers as Nat × Nat modulo (a,b) ~ (c,d) iff a+d = b+c
def intRel (p q : Nat × Nat) : Prop :=
  p.1 + q.2 = p.2 + q.1

def MyInt := Quot intRel

def MyInt.mk (a b : Nat) : MyInt := Quot.mk intRel (a, b)

-- (3,1) and (5,3) both represent 2
example : MyInt.mk 3 1 = MyInt.mk 5 3 :=
  Quot.sound (show 3 + 3 = 1 + 5 by omega)

-- Quot.lift has a computation rule:
-- Quot.lift f h (Quot.mk r a) reduces to f a
def MyInt.isZero : MyInt → Bool :=
  Quot.lift (fun p => p.1 == p.2) (by
    intro a b h
    simp [intRel, BEq.beq] at *
    omega)

#eval MyInt.isZero (MyInt.mk 3 3)  -- true
#eval MyInt.isZero (MyInt.mk 3 1)  -- false


-- ============================================================
-- Part V: Classical Choice
-- ============================================================

#check @Classical.choice  -- {α : Sort u} → Nonempty α → α

-- Classical.choose extracts a witness from ∃
-- (bypassing large elimination restriction)
#check @Classical.choose      -- (h : ∃ x, p x) → α
#check @Classical.choose_spec -- (h : ∃ x, p x) → p (choose h)

-- You CANNOT write h.1 to extract the witness:
-- example (h : ∃ n : Nat, n > 5) : Nat := h.1
-- Error: cannot eliminate from Prop to Type

-- But Classical.choose can:
noncomputable def extractWitness (h : ∃ n : Nat, n > 5) : Nat :=
  Classical.choose h

-- Classical.em is a theorem (derived from the three axioms):
#check @Classical.em  -- ∀ (p : Prop), p ∨ ¬p
#print axioms Classical.em  -- propext, Quot.sound, Classical.choice

-- Double negation elimination
theorem dne (p : Prop) : ¬¬p → p := by
  intro hnn
  cases Classical.em p with
  | inl hp => exact hp
  | inr hnp => exact absurd hnp hnn


-- ============================================================
-- Part V: Diaconescu's Theorem (full proof)
-- ============================================================

-- We prove: propext + funext + Classical.choice → p ∨ ¬p
-- Following TPIL Chapter 12.

open Classical in
noncomputable def diaconescu (p : Prop) : p ∨ ¬p := by
  -- Step 1: Define two predicates on Prop
  let U (x : Prop) : Prop := x = True ∨ p
  let V (x : Prop) : Prop := x = False ∨ p

  -- Step 2: Both are nonempty (witnessed by True and False)
  have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
  have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩

  -- Step 3: Use choice to pick elements u ∈ U and v ∈ V
  let u : Prop := choose exU
  let v : Prop := choose exV
  have u_def : U u := choose_spec exU
  have v_def : V v := choose_spec exV

  -- Step 4: Either u ≠ v, or p is true.
  -- Case analysis on u_def and v_def (each is a disjunction).
  -- In three of four cases, p is true directly.
  -- In the remaining case (u = True, v = False), u ≠ v.
  have not_uv_or_p : u ≠ v ∨ p := by
    match u_def, v_def with
    | Or.inr hp, _          => exact Or.inr hp
    | _,         Or.inr hp  => exact Or.inr hp
    | Or.inl hu, Or.inl hv  =>
      -- hu : u = True,  hv : v = False
      -- so u ≠ v (otherwise True = False)
      exact Or.inl fun heq =>
        -- heq : u = v
        -- hu.symm : True = u, heq : u = v, hv : v = False
        -- chain: True = u = v = False
        have h : True = False := hu.symm.trans (heq.trans hv)
        -- transport True.intro along True = False to get False
        Eq.mp h True.intro

  -- Step 5: If p is true, then U = V (by propext + funext),
  -- so u and v were chosen from the same predicate, hence u = v.
  have p_implies_uv : p → u = v := fun hp => by
    -- When p holds, both predicates become trivially true:
    -- U x = (x = True ∨ p) = True, V x = (x = False ∨ p) = True
    have hpred : U = V := funext fun x =>
      propext ⟨fun _ => Or.inr hp, fun _ => Or.inr hp⟩
    -- After rewriting U to V, the two choose calls have the
    -- same predicate. By proof irrelevance the existential proofs
    -- are equal, so the results are equal.
    show choose exU = choose exV
    have h₀ : ∀ (e₁ : ∃ x, U x) (e₂ : ∃ x, V x),
        @choose _ U e₁ = @choose _ V e₂ := by
      rw [hpred]    -- replaces U with V in the goal
      intros; rfl   -- by proof irrelevance, e₁ = e₂
    exact h₀ exU exV

  -- Step 6: Combine steps 4 and 5.
  -- not_uv_or_p : u ≠ v ∨ p
  -- p_implies_uv : p → u = v
  -- If u ≠ v: then ¬p (contrapositive of p_implies_uv)
  -- If p: then p directly.
  match not_uv_or_p with
  | Or.inl hne => exact Or.inr (mt p_implies_uv hne)
  | Or.inr hp  => exact Or.inl hp


-- ============================================================
-- Part VI: propDecidable (every Prop is decidable)
-- ============================================================

-- Recall: Decidable p is an inductive in Type with two constructors.
-- We cannot match on p ∨ ¬p (in Prop, two constructors) to produce
-- Decidable p (in Type) — large elimination forbids this.
-- The trick: match into Nonempty (Decidable p) (Prop → Prop, OK),
-- then use Classical.choice to extract.

open Classical in
noncomputable def propDecidable' (p : Prop) : Decidable p :=
  choice (match em p with
  | Or.inl hp  => ⟨Decidable.isTrue hp⟩
  | Or.inr hnp => ⟨Decidable.isFalse hnp⟩ )

-- Check: uses all three axioms
#print axioms propDecidable'


-- ============================================================
-- Part VII: The Spectrum
-- ============================================================

-- Pure: no axioms
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

#print axioms factorial  -- no axioms

-- Compatible with compilation
def abs' (x : Int) : Int :=
  if x ≥ 0 then x else -x

#print axioms abs'

-- Noncomputable
-- Nat.Prime is in Mathlib, not core Lean.
-- We use a simple predicate instead for illustration.
def IsOdd (n : Nat) : Prop := n % 2 = 1

noncomputable def choose_odd (n : Nat)
    (h : ∃ p, p > n ∧ IsOdd p) : Nat :=
  Classical.choose h

-- The witness is inside h, but ∃ lives in Prop.
-- Large elimination forbids: def bad := h.1
-- Classical.choose bypasses via Classical.choice.

#print axioms choose_odd


-- ============================================================
-- Exercises
-- ============================================================

-- Exercise 1: check axioms
#print axioms Nat.add_comm
#print axioms List.length_map
#print axioms Classical.em

-- Exercise 2: Unordered pairs
def swapRel (p q : α × α) : Prop :=
  (p.1 = q.1 ∧ p.2 = q.2) ∨ (p.1 = q.2 ∧ p.2 = q.1)

def UPair (α : Type) := Quot (@swapRel α)

def UPair.mk (a b : α) : UPair α := Quot.mk swapRel (a, b)

theorem UPair.comm (a b : α) : UPair.mk a b = UPair.mk b a :=
  Quot.sound (Or.inr ⟨rfl, rfl⟩)

-- Exercise 3: double negation elimination (proved above as dne)
#print axioms dne

-- Exercise 4: Set intersection commutativity (proved above)
#print axioms MySet.inter_comm

-- Exercise 5: Diaconescu (proved above as diaconescu)
#print axioms diaconescu

end Lec24
