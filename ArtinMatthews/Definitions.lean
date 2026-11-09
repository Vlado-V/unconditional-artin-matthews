module

public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic


set_option backward.privateInPublic true
@[expose] public section

/-!
# Exact arithmetic predicates for the Artin–Matthews paper

The finite set contains distinct integer bases. Rational squares and negative
three times rational squares exclude the zero square, as in Q×² in the paper.
No assertion of the unproved analytic implication is made in this module.
-/

namespace ArtinMatthews

/-- The paper's hypotheses on the finite set of bases. -/
def AdmissibleBases (S : Finset ℤ) : Prop :=
  S.Nonempty ∧ ∀ a ∈ S, a ≠ 0 ∧ a ≠ 1 ∧ a ≠ -1

/-- A nonzero square in ℚ. -/
def RationalSquare (z : ℤ) : Prop :=
  ∃ q : ℚ, q ≠ 0 ∧ q ^ 2 = (z : ℚ)

/-- A number in -3 ℚ×². -/
def NegativeThreeRationalSquare (z : ℤ) : Prop :=
  ∃ q : ℚ, q ≠ 0 ∧ (z : ℚ) = -3 * q ^ 2

/-- Condition (A): an odd subset product is a nonzero rational square. -/
def ObstructionA (S : Finset ℤ) : Prop :=
  ∃ T : Finset ℤ, T ⊆ S ∧ Odd T.card ∧ RationalSquare (∏ a ∈ T, a)

/-- Cubes modulo a prime include zero. -/
def IsCubeMod (p : ℕ) (a : ℤ) : Prop :=
  ∃ b : ZMod p, b ^ 3 = (a : ZMod p)

/-- Condition (B), including its universal condition on split cubic primes. -/
def ObstructionB (S : Finset ℤ) : Prop :=
  (∃ T : Finset ℤ, T ⊆ S ∧ Even T.card ∧
    NegativeThreeRationalSquare (∏ a ∈ T, a)) ∧
  ∀ p : ℕ, p.Prime → p % 3 = 1 → ∃ a ∈ S, IsCubeMod p a

/-- An integer is a primitive root modulo p, including the nonzero condition. -/
def IsPrimitiveRootMod (p : ℕ) (a : ℤ) : Prop :=
  (a : ZMod p) ≠ 0 ∧ orderOf (a : ZMod p) = p - 1

/-- The paper's set P_S. -/
def SimultaneousPrimitivePrimes (S : Finset ℤ) : Set ℕ :=
  {p | p.Prime ∧ ∀ a ∈ S, IsPrimitiveRootMod p a}

/-- The dyadic counting function in (1.1), for a real cutoff. -/
noncomputable def dyadicCount (S : Finset ℤ) (x : ℝ) : ℕ := by
  classical
  exact ((Finset.range (⌊2 * max x 0⌋₊ + 1)).filter
    fun (p : ℕ) => x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧ p ∈ SimultaneousPrimitivePrimes S).card

/-- The exact positive lower bound asserted by Theorem 1.1. -/
def PositiveDyadicLowerBound (S : Finset ℤ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, 1 < x₀ ∧
    ∀ x : ℝ, x₀ ≤ x → c * x / Real.log x ≤ (dyadicCount S x : ℝ)

/-- Statement of the two conclusions in Theorem 1.1; this is a definition,
not a theorem asserting its presently unformalized analytic proof. -/
def MainStatement : Prop :=
  ∀ S : Finset ℤ, AdmissibleBases S →
    ((¬ ObstructionA S ∧ ¬ ObstructionB S) → PositiveDyadicLowerBound S) ∧
    ((ObstructionA S ∨ ObstructionB S) → (SimultaneousPrimitivePrimes S).Finite)

end ArtinMatthews
