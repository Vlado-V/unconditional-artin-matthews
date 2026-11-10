module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import ArtinMatthews.ShiftedVoronoiBessel
public import ArtinMatthews.ShiftedVoronoiBesselMonomial


set_option backward.privateInPublic true
@[expose] public section

/-!
# The exponential-test integral for the weight-one Bessel kernel

The proof uses the actual `Complex.besselJ` series, evaluates each damped
monomial by the Gamma integral, and justifies the interchange by summability
of the integrals of the absolute values.
-/

noncomputable section
open MeasureTheory Set Complex

namespace ArtinMatthews

private def besselLaplaceTerm (a b : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  (((-b) ^ n / (n.factorial : ℝ) ^ 2 * (x ^ n * Real.exp (-(a * x))) : ℝ) : ℂ)

private theorem besselLaplaceTerm_integrable (a b : ℝ) (ha : 0 < a) (n : ℕ) :
    IntegrableOn (besselLaplaceTerm a b n) (Ioi 0) :=
  ((integrableOn_pow_mul_exp_neg_mul_Ioi a ha n).const_mul _).ofReal

private theorem besselLaplaceTerm_integral (a b : ℝ) (ha : 0 < a) (n : ℕ) :
    (∫ x in Ioi 0, besselLaplaceTerm a b n x) =
      ((1 / a * ((-b / a) ^ n / (n.factorial : ℝ)) : ℝ) : ℂ) := by
  simp only [besselLaplaceTerm]
  rw [integral_complex_ofReal, integral_const_mul,
    integral_pow_mul_exp_neg_mul_Ioi a ha n]
  congr 1
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  simp only [div_pow, pow_succ]
  field_simp

private theorem besselLaplaceTerm_norm_integral (a b : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (n : ℕ) :
    (∫ x in Ioi 0, ‖besselLaplaceTerm a b n x‖) =
      1 / a * ((b / a) ^ n / (n.factorial : ℝ)) := by
  have he : (∫ x in Ioi 0, ‖besselLaplaceTerm a b n x‖) =
      ∫ x in Ioi 0, b ^ n / (n.factorial : ℝ) ^ 2 *
        (x ^ n * Real.exp (-(a * x))) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change ‖((((-b) ^ n / (n.factorial : ℝ) ^ 2) *
      (x ^ n * Real.exp (-(a * x))) : ℝ) : ℂ)‖ = _
    rw [Complex.norm_real, Real.norm_eq_abs]
    simp only [abs_mul, abs_div, abs_pow, abs_neg, abs_of_nonneg hb,
      abs_of_nonneg (show (0 : ℝ) ≤ n.factorial from Nat.cast_nonneg _),
      abs_of_nonneg (show 0 ≤ x from hx.le), abs_of_pos (Real.exp_pos _)]
  rw [he, integral_const_mul, integral_pow_mul_exp_neg_mul_Ioi a ha n]
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  simp only [div_pow, pow_succ]
  field_simp

private theorem hasSum_besselLaplaceTerm (a b x : ℝ) (hb : 0 ≤ b) (hx : 0 < x) :
    HasSum (fun n ↦ besselLaplaceTerm a b n x)
      ((Real.exp (-(a * x)) : ℂ) * Complex.besselJ 0 (2 * (Real.sqrt (b * x) : ℂ))) := by
  convert (hasSum_besselJ_zero_sqrt (b * x) (mul_nonneg hb hx.le)).mul_left
    (Real.exp (-(a * x)) : ℂ) using 1
  funext n
  simp only [besselLaplaceTerm, ofReal_mul, ofReal_div, ofReal_pow, ofReal_neg,
    ofReal_natCast, ← neg_mul, mul_pow]
  ring

/-- The Laplace integral of the actual order-zero Bessel kernel. -/
theorem integral_exp_mul_besselJ_zero_sqrt (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    (∫ x : ℝ in Ioi 0,
      (Real.exp (-(a * x)) : ℂ) * Complex.besselJ 0 (2 * (Real.sqrt (b * x) : ℂ))) =
        ((1 / a * Real.exp (-b / a) : ℝ) : ℂ) := by
  have hnorm : Summable (fun n : ℕ ↦ ∫ x in Ioi 0, ‖besselLaplaceTerm a b n x‖) := by
    simp only [besselLaplaceTerm_norm_integral a b ha hb]
    exact (NormedSpace.expSeries_div_hasSum_exp (b / a)).summable.mul_left (1 / a)
  have hi := integral_tsum_of_summable_integral_norm
    (fun n ↦ besselLaplaceTerm_integrable a b ha n) hnorm
  rw [show (∫ x : ℝ in Ioi 0,
      (Real.exp (-(a * x)) : ℂ) * Complex.besselJ 0 (2 * (Real.sqrt (b * x) : ℂ))) =
        ∫ x in Ioi 0, ∑' n, besselLaplaceTerm a b n x by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x hx
          exact (hasSum_besselLaplaceTerm a b x hb hx).tsum_eq.symm,
    ← hi]
  simp only [besselLaplaceTerm_integral a b ha]
  have hs := Complex.hasSum_ofReal.mpr
    ((NormedSpace.expSeries_div_hasSum_exp (-b / a)).mul_left (1 / a))
  simpa only [← Real.exp_eq_exp_ℝ] using hs.tsum_eq

end ArtinMatthews
