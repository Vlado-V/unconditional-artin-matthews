module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import ArtinMatthews.SpectralGammaHalfInteger
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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


set_option backward.privateInPublic true
@[expose] public section

/-! Exact identification of the integrated even exponential coefficient with
the defining regularized hypergeometric Bessel coefficient. -/
noncomputable section
namespace ArtinMatthews

open Complex

theorem spectralPoisson_even_coefficient (ν : ℂ)
    (hν : -(1 / 2 : ℝ) < ν.re) (x : ℂ) (n : ℕ) :
    (Complex.I * x) ^ (2 * n) / ((2 * n).factorial : ℂ) *
      Complex.betaIntegral ((n : ℂ) + 1 / 2) (ν + 1 / 2) =
    (Real.sqrt Real.pi : ℂ) * Complex.Gamma (ν + 1 / 2) *
      ((-(x / 2) ^ 2) ^ n / ((n.factorial : ℂ) * Complex.Gamma (ν + 1 + n))) := by
  have hleft : 0 < ((n : ℂ) + 1 / 2).re := by
    norm_num
    positivity
  have hright : 0 < (ν + 1 / 2).re := by
    norm_num
    linarith
  have hg : Complex.Gamma (ν + 1 + n) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    norm_num
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn2 : ((2 * n).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2 * n)
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ hleft hright,
    spectral_gamma_nat_add_half,
    show (n : ℂ) + 1 / 2 + (ν + 1 / 2) = ν + 1 + n by ring]
  rw [neg_pow]
  simp only [div_pow, mul_pow, pow_mul, Complex.I_sq]
  norm_num
  field_simp [hn, hn2, hg]

end ArtinMatthews
