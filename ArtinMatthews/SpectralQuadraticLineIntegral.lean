module

public import ArtinMatthews.SpectralQuadraticBetaIntegral


set_option backward.privateInPublic true
@[expose] public section

/-! Exact full-line slices of a positive quadratic form, with the
absolute convergence and height factors needed for dimensional reduction. -/

noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

theorem spectralQuadraticLine_factor (s : ℂ) {a : ℝ} (ha : 0 < a) (u : ℝ) :
    ((a+u^2 : ℝ) : ℂ)^(-s) =
      (a : ℂ)^(-s)*spectralQuadraticPower s (u/Real.sqrt a) := by
  have hr : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsq := Real.sq_sqrt ha.le
  have he : a+u^2 = a*(1+(u/Real.sqrt a)^2) := by
    field_simp [hr.ne']
    nlinarith
  rw [he,Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg ha.le (by positivity)]
  simp only [spectralQuadraticPower,Complex.ofReal_add,Complex.ofReal_one,Complex.ofReal_pow]

theorem spectralQuadraticLine_integrable (s : ℂ) (hs : 1/2 < s.re) {a : ℝ} (ha : 0 < a) :
    Integrable (fun u : ℝ => ((a+u^2 : ℝ) : ℂ)^(-s)) := by
  have h := (spectralQuadraticPower_integrable s hs).comp_mul_right'
    (inv_ne_zero (Real.sqrt_pos.mpr ha).ne')
  have he : (fun u : ℝ => ((a+u^2 : ℝ) : ℂ)^(-s)) =
      fun u => (a : ℂ)^(-s)*spectralQuadraticPower s (u/Real.sqrt a) :=
    funext (spectralQuadraticLine_factor s ha)
  rw [he]
  simpa only [div_eq_mul_inv] using h.const_mul ((a : ℂ)^(-s))

theorem spectralQuadraticLine_integral (s : ℂ) (hs : 1/2 < s.re) {a : ℝ} (ha : 0 < a) :
    (∫ u : ℝ, ((a+u^2 : ℝ) : ℂ)^(-s)) =
      (a : ℂ)^(1/2-s)*((Real.sqrt Real.pi : ℂ)*Complex.Gamma (s-1/2)/Complex.Gamma s) := by
  simp_rw [spectralQuadraticLine_factor s ha]
  rw [integral_const_mul,Measure.integral_comp_div,
    abs_of_pos (Real.sqrt_pos.mpr ha),Complex.real_smul,spectralQuadraticPower_integral s hs]
  have hroot : (Real.sqrt a : ℂ) = (a : ℂ)^(1/2 : ℂ) := by
    rw [Real.sqrt_eq_rpow,Complex.ofReal_cpow ha.le]
    norm_num
  rw [hroot]
  have he : (a : ℂ)^(-s)*(a : ℂ)^(1/2 : ℂ) = (a : ℂ)^(1/2-s) := by
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ha.ne')]
    congr 1
    ring
  calc
    _ = ((a : ℂ)^(-s)*(a : ℂ)^(1/2 : ℂ))*
      ((Real.sqrt Real.pi : ℂ)*Complex.Gamma (s-1/2)/Complex.Gamma s) := by ring
    _ = _ := by rw [he]

end ArtinMatthews

