module

public import OAI.NumberTheory.Jacobsthal.Analysis.BonferroniDensity
public import ArtinMatthews.RoughBonferroniDivisors
public import ArtinMatthews.RoughBonferroniInterval
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Factorial and numeric-size forms of the actual next-layer remainder. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators
open Finset
open OAI.Erdos970.NumberTheoryLean.BonferroniDensity

theorem rough_layer_reciprocal_mass_eq (P : Finset ℕ) (k : ℕ) :
    (∑ S ∈ P.powersetCard k, 1 / (roughSubsetDivisor S : ℝ)) =
      elementarySum P (fun p => 1 / (p : ℝ)) k := by
  simp [elementarySum, roughSubsetDivisor]

/-- Exact factorial saving in the actual squarefree-divisor layer. -/
theorem rough_layer_reciprocal_mass_le_factorial (P : Finset ℕ) (k : ℕ) :
    (∑ S ∈ P.powersetCard k, 1 / (roughSubsetDivisor S : ℝ)) ≤
      (∑ p ∈ P, 1 / (p : ℝ)) ^ k / (k.factorial : ℝ) := by
  rw [rough_layer_reciprocal_mass_eq]
  exact elementarySum_le_pow_div_factorial P _ (fun _ _ => by positivity)
    (sum_nonneg (fun _ _ => by positivity)) le_rfl k

theorem rough_layer_reciprocal_mass_le_of_sum_le (P : Finset ℕ) (k : ℕ)
    {A : ℝ} (hA : 0 ≤ A) (hsum : ∑ p ∈ P, 1 / (p : ℝ) ≤ A) :
    (∑ S ∈ P.powersetCard k, 1 / (roughSubsetDivisor S : ℝ)) ≤
      A ^ k / (k.factorial : ℝ) := by
  rw [rough_layer_reciprocal_mass_eq]
  exact elementarySum_le_pow_div_factorial P _ (fun _ _ => by positivity) hA hsum k

/-- A layer of subsets of primes at most `v` has at most `v^k` members. -/
theorem rough_layer_card_le_pow (P : Finset ℕ) (k v : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hheight : ∀ p ∈ P, p ≤ v) :
    (P.powersetCard k).card ≤ v ^ k := by
  have hcard : P.card ≤ v := by
    calc
      P.card ≤ (Icc 1 v).card := card_le_card (fun p hp =>
        mem_Icc.mpr ⟨(hprime p hp).pos, hheight p hp⟩)
      _ = v := by simp
  rw [card_powersetCard]
  exact (Nat.choose_le_pow P.card k).trans (Nat.pow_le_pow_left hcard k)

/-- Numerical finite error bound, ready for the separate factorial-tail
and logarithmic-parameter estimates. -/
theorem roughDivisorPolynomial_weighted_Ioc_error_numeric
    (P : Finset ℕ) (r M N v : ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hheight : ∀ p ∈ P, p ≤ v) (a : ℕ → ℂ)
    (ha : ∀ n ∈ Ioc M N, ‖a n‖ ≤ 1) :
    ‖(∑ n ∈ Ioc M N, (if ∀ p ∈ P, ¬ p ∣ n then (1 : ℂ) else 0) * a n) -
      ∑ n ∈ Ioc M N, roughDivisorPolynomial P r n * a n‖ ≤
      ((N - M : ℕ) : ℝ) *
        ((∑ p ∈ P, 1 / (p : ℝ)) ^ (r + 1) / ((r + 1).factorial : ℝ)) +
      (v : ℝ) ^ (r + 1) := by
  apply (roughDivisorPolynomial_weighted_Ioc_error_le P r M N hprime a ha).trans
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (rough_layer_reciprocal_mass_le_factorial P (r + 1))
      (Nat.cast_nonneg _)
  · exact_mod_cast rough_layer_card_le_pow P (r + 1) v hprime hheight

end ArtinMatthews
