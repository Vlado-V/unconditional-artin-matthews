module

public import Mathlib.Analysis.SpecialFunctions.Bessel
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! The literal defining series of Mathlib's complex-order Bessel J. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators

/-- The normalized hypergeometric series occurring in the actual Bessel function. -/
theorem besselJ_eq_hypergeometric_tsum (ν x : ℂ) :
    Complex.besselJ ν x = (x / 2) ^ ν *
      ∑' n : ℕ, (-(x / 2) ^ 2) ^ n /
        ((n.factorial : ℂ) * Complex.Gamma (ν + 1 + n)) := by
  unfold Complex.besselJ Complex.regularizedHGFun Complex.regularizedHGFunSeries
  rw [← FormalMultilinearSeries.ofScalarsSum, FormalMultilinearSeries.ofScalars_sum_eq]
  congr 1
  apply tsum_congr
  intro n
  simp [Complex.regularizedHGFunCoeff, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- Absolute convergence of the actual normalized Bessel series at every argument. -/
theorem besselJ_hypergeometric_summable (ν x : ℂ) :
    Summable (fun n : ℕ => (-(x / 2) ^ 2) ^ n /
      ((n.factorial : ℂ) * Complex.Gamma (ν + 1 + n))) := by
  have h := (Complex.regularizedHGFunSeries 0 {ν + 1}).summable
    (x := -(x / 2) ^ 2) (by simp)
  simpa [Complex.regularizedHGFunSeries, FormalMultilinearSeries.ofScalars_apply_eq,
    Complex.regularizedHGFunCoeff, smul_eq_mul, div_eq_mul_inv, mul_comm] using h

end ArtinMatthews
