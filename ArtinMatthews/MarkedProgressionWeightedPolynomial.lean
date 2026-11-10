module

public import ArtinMatthews.MarkedProgressionWeighted
public import ArtinMatthews.MarkedProgressionCoefficients
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! One finite indexed divisor polynomial for all retained weighted layers.
The index remembers its degree and prime subset; divisors need not be distinct. -/

namespace ArtinMatthews

open OAI.Erdos970.NumberTheoryLean
open scoped BigOperators

abbrev MarkedWeightedIndex := Σ _ : ℕ, Finset ℕ

noncomputable def markedWeightedIndices (P S : Finset ℕ) (k : ℕ) : Finset MarkedWeightedIndex :=
  (Finset.range (k + 1)).sigma (fun j => (P \ S).powersetCard j)

noncomputable def markedWeightedDivisor (S : Finset ℕ) (i : MarkedWeightedIndex) : ℕ :=
  ∏ p ∈ S ∪ i.2, p

noncomputable def markedWeightedCoefficient (θ : ℕ → ℝ) (i : MarkedWeightedIndex) : ℝ :=
  (-1 : ℝ) ^ i.1 * ∏ p ∈ i.2, θ p

theorem markedWeightedTruncation_eq_polynomial (P S : Finset ℕ) (θ : ℕ → ℝ) (k u : ℕ) :
    markedWeightedTruncation P S θ k u =
      markedIndexedDivisorPolynomial (markedWeightedIndices P S k)
        (markedWeightedDivisor S) (markedWeightedCoefficient θ) u := by
  classical
  unfold markedWeightedTruncation markedWeightedTail markedIndexedDivisorPolynomial
    markedWeightedIndices markedWeightedDivisor markedWeightedCoefficient
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  split_ifs <;> simp

theorem markedWeightedDivisor_pos (P S : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hS : S ⊆ P) {k : ℕ} {i : MarkedWeightedIndex} (hi : i ∈ markedWeightedIndices P S k) :
    0 < markedWeightedDivisor S i := by
  classical
  have hT := (Finset.mem_powersetCard.mp (Finset.mem_sigma.mp hi).2).1
  apply Finset.prod_pos
  intro p hp
  exact (hP p (Finset.mem_union.mp hp |>.elim (fun h => hS h)
    (fun h => (Finset.mem_sdiff.mp (hT h)).1))).pos

/-- The polynomial model is exactly the truncated weighted Euler product. -/
theorem markedWeightedCoefficient_reciprocal_sum (P S : Finset ℕ) (θ : ℕ → ℝ) (k : ℕ) :
    (∑ i ∈ markedWeightedIndices P S k,
      markedWeightedCoefficient θ i / (markedWeightedDivisor S i : ℝ)) =
      (1 / (∏ p ∈ S, p : ℕ)) *
        BonferroniDensity.densityPolynomial k (P \ S) (fun p => θ p / (p : ℝ)) := by
  classical
  unfold markedWeightedIndices markedWeightedCoefficient markedWeightedDivisor
    BonferroniDensity.densityPolynomial
  rw [Finset.sum_sigma, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = (-1 : ℝ) ^ j * ∑ T ∈ (P \ S).powersetCard j,
        (∏ p ∈ T, θ p) / (∏ p ∈ S ∪ T, p : ℕ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T _
      ring
    _ = _ := by rw [marked_weighted_selected_reciprocal_mass]; ring

/-- Retained coefficients have the same uniform mass bound even when the
marking damping varies from band to band. -/
theorem markedWeightedCoefficient_mass_le (P S : Finset ℕ) (θ : ℕ → ℝ)
    (hθ : ∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) (k : ℕ) :
    (∑ i ∈ markedWeightedIndices P S k, |markedWeightedCoefficient θ i|) ≤
      (k + 1 : ℕ) * (max 1 ((P \ S).card : ℝ)) ^ k := by
  classical
  unfold markedWeightedIndices markedWeightedCoefficient
  rw [Finset.sum_sigma]
  apply le_trans _ (marked_truncation_coefficient_mass_le (P \ S) k (θ := 1) (by norm_num) le_rfl)
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro T hT
  have ht : ∀ p ∈ T, 0 ≤ θ p ∧ θ p ≤ 1 := fun p hp =>
    hθ p (Finset.mem_sdiff.mp ((Finset.mem_powersetCard.mp hT).1 hp)).1
  have hnonneg : 0 ≤ ∏ p ∈ T, θ p := Finset.prod_nonneg (fun p hp => (ht p hp).1)
  have hle : (∏ p ∈ T, θ p) ≤ 1 := Finset.prod_le_one₀ (fun p hp => (ht p hp).1)
    (fun p hp => (ht p hp).2)
  simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg hnonneg,
    mul_one] using hle

end ArtinMatthews
