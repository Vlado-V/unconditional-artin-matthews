module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Data.Set.Card
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Order.LiminfLimsup

@[expose] public section

namespace ArtinMatthews

open Filter
open scoped Topology Classical

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

/-- Number of simultaneous primitive-root primes up to a natural cutoff. -/
noncomputable def primeCount (S : Finset ℤ) (n : ℕ) : ℕ := by
  classical
  exact (n.primesLE.filter fun p => p ∈ SimultaneousPrimitivePrimes S).card

/-- Number of simultaneous primitive-root primes in the real interval `[1,x]`. -/
noncomputable def realPrimeCount (S : Finset ℤ) (x : ℝ) : ℕ :=
  primeCount S ⌊x⌋₊

/-- Relative prime density at a real cutoff, as in the paper. -/
noncomputable def realRelativePrimeDensity (S : Finset ℤ) (x : ℝ) : ℝ :=
  (realPrimeCount S x : ℝ) / (Nat.primeCounting ⌊x⌋₊ : ℝ)

/-- The paper's positivity condition, using real cutoffs. -/
def PositiveRealLowerRelativePrimeDensity (S : Finset ℤ) : Prop :=
  0 < liminf (realRelativePrimeDensity S) atTop

end ArtinMatthews

namespace ArtinMatthewsPaper

open ArtinMatthews

/-- Theorem 1.1 of the accompanying Artin–Matthews paper. -/
theorem main_result :
  ∀ S : Finset ℤ, AdmissibleBases S →
    ((¬ ObstructionA S ∧ ¬ ObstructionB S) →
      PositiveDyadicLowerBound S ∧ PositiveRealLowerRelativePrimeDensity S) ∧
    ((ObstructionA S ∨ ObstructionB S) → (SimultaneousPrimitivePrimes S).Finite) := by
  sorry

end ArtinMatthewsPaper
