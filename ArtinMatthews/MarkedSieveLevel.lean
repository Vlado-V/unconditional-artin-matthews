module

public import ArtinMatthews.MarkedEstimateSieveParameters
public import OAI.NumberTheory.Jacobsthal.Estimates.FundamentalBlockEstimate
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

/-! The actual finite sieve divisor level lies inside the progression range
when the power cutoff is chosen by the already proved parameter formula. -/

namespace ArtinMatthews

open OAI.Erdos970.NumberTheoryLean

/-- Exact floor-power level comparison, with no asymptotic assumption. -/
theorem marked_floor_power_le (x γ c : ℝ) (N : ℕ)
    (hx : 1 ≤ x) (hlevel : γ * (N : ℝ) ≤ c) :
    ⌊x ^ γ⌋₊ ^ N ≤ ⌊x ^ c⌋₊ := by
  apply (Nat.le_floor_iff (Real.rpow_nonneg (le_trans zero_le_one hx) c)).mpr
  rw [Nat.cast_pow]
  calc
    (⌊x ^ γ⌋₊ : ℝ) ^ N ≤ (x ^ γ) ^ N :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le (Real.rpow_nonneg (le_trans zero_le_one hx) γ)) N
    _ = x ^ (γ * (N : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_trans zero_le_one hx)]
    _ ≤ x ^ c := Real.rpow_le_rpow_of_exponent_le hx hlevel

/-- Every divisor entering the proved fundamental sieve is a positive
modulus in the full available progression range. -/
theorem marked_sieve_level_subset (P : Finset ℕ) (x γ c : ℝ) (N : ℕ)
    (hx : 1 ≤ x) (hlevel : γ * (N : ℝ) ≤ c) :
    FundamentalBlockEstimate.levelDivisors P (⌊x ^ γ⌋₊ ^ N) ⊆ Finset.Icc 1 ⌊x ^ c⌋₊ := by
  intro d hd
  obtain ⟨hdiv, hsize⟩ := Finset.mem_filter.mp hd
  exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hdiv,
    hsize.trans (marked_floor_power_le x γ c N hx hlevel)⟩

/-- The fixed positive sieve exponent leaves half of the available
progression exponent in reserve. -/
theorem marked_sieve_parameter_level_subset (P : Finset ℕ) (x c : ℝ) (m : ℕ)
    (hx : 1 ≤ x) (hc : 0 ≤ c) :
    FundamentalBlockEstimate.levelDivisors P
      (⌊x ^ markedSieveExponent c m⌋₊ ^ (12 * (m + 1))) ⊆ Finset.Icc 1 ⌊x ^ c⌋₊ := by
  apply marked_sieve_level_subset P x (markedSieveExponent c m) c (12 * (m + 1)) hx
  have heq := markedSieveExponent_level c m
  push_cast
  nlinarith

end ArtinMatthews
