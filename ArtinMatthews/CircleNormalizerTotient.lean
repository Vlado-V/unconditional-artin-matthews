module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
public import OAI.NumberTheory.Jacobsthal.Sieve.DivisorLogGrowth


set_option backward.privateInPublic true
@[expose] public section

/-! A proved subpower lower bound for Euler's totient, using the existing
divisor subpower estimate and the exact divisor sum of the totient. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators

theorem circle_self_le_totient_mul_divisors (n : ℕ) (hn : 0 < n) :
    n ≤ n.totient * n.divisors.card := by
  calc
    n = ∑ d ∈ n.divisors, d.totient := (Nat.sum_totient n).symm
    _ ≤ ∑ _d ∈ n.divisors, n.totient := by
      apply Finset.sum_le_sum
      intro d hd
      exact Nat.le_of_dvd (Nat.totient_pos.mpr hn)
        (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd))
    _ = _ := by simp [Nat.mul_comm]

/-- This is the elementary totient lower bound underlying the normalizer
estimate. Its constant is uniform in the integer argument. -/
theorem circle_totient_ge_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n →
      c * (n : ℝ) ^ (1 - ε) ≤ n.totient := by
  obtain ⟨C, hC, hτ⟩ :=
    OAI.Erdos970.ErdosDivisorBounds.divisor_power_subpower 1 hε
  refine ⟨C⁻¹, inv_pos.mpr hC, fun n hn => ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hφ : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr hn
  have hpow : 0 < (n : ℝ) ^ ε := Real.rpow_pos_of_pos hnR ε
  have hτn := hτ n hn
  simp only [pow_one] at hτn
  have hnφ : (n : ℝ) ≤ (n.totient : ℝ) * n.divisors.card := by
    exact_mod_cast circle_self_le_totient_mul_divisors n hn
  have h : (n : ℝ) ≤ C * (n : ℝ)^ε * n.totient := by
    nlinarith [mul_le_mul_of_nonneg_left hτn hφ.le]
  rw [Real.rpow_sub hnR, Real.rpow_one]
  have heq : C⁻¹ * ((n : ℝ) / (n : ℝ)^ε) = (n : ℝ) / (C * (n : ℝ)^ε) := by
    field_simp
  rw [heq]
  exact (div_le_iff₀ (mul_pos hC hpow)).mpr (by simpa [mul_comm] using h)

theorem circle_totient_ge_sqrt :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n → c * Real.sqrt n ≤ n.totient := by
  obtain ⟨c, hc, h⟩ := circle_totient_ge_rpow (1/2) (by norm_num)
  refine ⟨c, hc, fun n hn => ?_⟩
  simpa only [show (1 : ℝ) - 1/2 = 1/2 by norm_num, Real.sqrt_eq_rpow] using h n hn

end ArtinMatthews
