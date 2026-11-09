module

public import ArtinMatthews.SpectralBetaExponential


set_option backward.privateInPublic true
@[expose] public section

/-! Actual beta moments convert the exponential integral to its
confluent gamma series. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace ArtinMatthews

theorem spectralUnitBeta_moment (a b : ℂ) (n : ℕ) :
    (∫ t : ℝ in (0 : ℝ)..1, (t : ℂ)^n*spectralUnitBetaProfile a b t) =
      Complex.betaIntegral (a+n) b := by
  rw [intervalIntegral.integral_of_le (by norm_num),integral_Ioc_eq_integral_Ioo,
    ← spectralUnitBetaProfile_integral]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  unfold spectralUnitBetaProfile
  calc
    _ = ((t : ℂ)^(n : ℂ)*(t : ℂ)^(a-1))*(1-(t : ℂ))^(b-1) := by
      rw [Complex.cpow_natCast]
      ring
    _ = _ := by
      rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht.1.ne')]
      congr 2
      ring

theorem spectralBeta_exponential_gamma_hasSum (a b z : ℂ) (ha : 0 < a.re) (hb : 0 < b.re) :
    HasSum (fun n : ℕ => Complex.Gamma (a+n)*z^n/
      ((n.factorial : ℂ)*Complex.Gamma (a+b+n)))
      ((∫ t : ℝ in (0 : ℝ)..1, Complex.exp (z*t)*spectralUnitBetaProfile a b t)/Complex.Gamma b) := by
  have hw : IntervalIntegrable (spectralUnitBetaProfile a b) volume 0 1 :=
    Complex.betaIntegral_convergent ha hb
  have h := (spectral_exp_unit_weight_integral_hasSum (spectralUnitBetaProfile a b) hw z).div_const
    (Complex.Gamma b)
  simp_rw [spectralUnitBeta_moment] at h
  convert h using 1
  funext n
  have han : 0 < (a+(n : ℂ)).re := by simp only [Complex.add_re,Complex.natCast_re]; positivity
  have habn : 0 < (a+b+(n : ℂ)).re := by
    simp only [Complex.add_re,Complex.natCast_re]
    positivity
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ han hb,
    show a+(n : ℂ)+b = a+b+n by ring]
  field_simp [Complex.Gamma_ne_zero_of_re_pos hb,Complex.Gamma_ne_zero_of_re_pos habn]

end ArtinMatthews
