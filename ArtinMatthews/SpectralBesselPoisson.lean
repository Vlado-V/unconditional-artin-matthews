module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import ArtinMatthews.SpectralBesselPoissonCoefficient
public import ArtinMatthews.SpectralBesselPoissonExponential
public import ArtinMatthews.SpectralBesselPoissonSeries
public import ArtinMatthews.SpectralBesselPoissonSymmetry
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! Poisson's integral formula for Mathlib's actual complex-order Bessel J,
derived from its defining hypergeometric series and genuine Beta moments. -/
noncomputable section
namespace ArtinMatthews

open MeasureTheory Set intervalIntegral Complex
open scoped BigOperators

/-- The genuine Poisson integral representation. The argument may be any
complex number; only the usual endpoint-integrability restriction on the order
is required. -/
theorem spectral_besselJ_poisson (ν x : ℂ) (hν : -(1 / 2 : ℝ) < ν.re) :
    Complex.besselJ ν x =
      (x / 2) ^ ν / ((Real.sqrt Real.pi : ℂ) * Complex.Gamma (ν + 1 / 2)) *
        ∫ u : ℝ in (-1 : ℝ)..1,
          Complex.exp (Complex.I * x * u) * (1 - (u : ℂ) ^ 2) ^ (ν - 1 / 2) := by
  let w : ℝ → ℂ := fun u => (1 - (u : ℂ) ^ 2) ^ (ν - 1 / 2)
  let G : ℂ := (Real.sqrt Real.pi : ℂ) * Complex.Gamma (ν + 1 / 2)
  let H : ℂ := ∑' n : ℕ, (-(x / 2) ^ 2) ^ n /
    ((n.factorial : ℂ) * Complex.Gamma (ν + 1 + n))
  let F : ℕ → ℂ := fun n => (Complex.I * x) ^ n / (n.factorial : ℂ) *
    ∫ u : ℝ in (-1 : ℝ)..1, spectralPoissonMoment ν n u
  have hw : IntervalIntegrable w volume (-1) 1 := by
    have hh := spectralPoissonMoment_integrable ν hν 0
    change IntervalIntegrable (fun u : ℝ => (u : ℂ) ^ 0 * w u) volume (-1) 1 at hh
    simpa only [pow_zero, one_mul] using hh
  have hfull : HasSum F (∫ u : ℝ in (-1 : ℝ)..1, Complex.exp (Complex.I * x * u) * w u) :=
    spectral_exp_weight_integral_hasSum w hw (Complex.I * x)
  have heven : HasSum (fun n => F (2 * n)) (G * H) := by
    convert (besselJ_hypergeometric_summable ν x).hasSum.mul_left G using 1
    funext n
    dsimp only [F]
    rw [spectralPoisson_even_moment ν hν n]
    exact spectralPoisson_even_coefficient ν hν x n
  have hodd : HasSum (fun n => F (2 * n + 1)) 0 := by
    simp only [F, spectralPoisson_odd_moment ν hν, mul_zero]
    exact hasSum_zero
  have hI : (∫ u : ℝ in (-1 : ℝ)..1, Complex.exp (Complex.I * x * u) * w u) = G * H := by
    simpa only [add_zero] using hfull.unique (heven.even_add_odd hodd)
  have hG : G ≠ 0 := by
    apply mul_ne_zero
    · exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
    · apply Complex.Gamma_ne_zero_of_re_pos
      norm_num
      linarith
  rw [besselJ_eq_hypergeometric_tsum]
  change (x / 2) ^ ν * H = (x / 2) ^ ν / G * _
  rw [hI]
  field_simp [hG]

end ArtinMatthews
