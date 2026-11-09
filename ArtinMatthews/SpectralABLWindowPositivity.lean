module

public import ArtinMatthews.SpectralABLCorrectedWindows


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open scoped BigOperators
noncomputable section

/-- The corrected regular window has nonnegative real value on the principal axis. -/
theorem spectralABLRegularCorrected_re_nonneg (T Δ t : ℝ) :
    0 ≤ (spectralABLRegularCorrected T Δ (t : ℂ)).re := by
  rw [spectralABLRegularCorrected_real, spectralABLRegularWindow_real,
    ← Complex.ofReal_div, Complex.ofReal_re]
  exact div_nonneg (spectralABLRegularWindowReal_nonneg T Δ t) (Real.cosh_pos _).le

theorem spectralABLRegularCorrected_norm_real (T Δ t : ℝ) :
    ‖spectralABLRegularCorrected T Δ (t : ℂ)‖ =
      spectralABLRegularWindowReal T Δ t / Real.cosh (Real.pi * t) := by
  rw [spectralABLRegularCorrected_real, spectralABLRegularWindow_real,
    ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (spectralABLRegularWindowReal_nonneg T Δ t)
      (Real.cosh_pos _).le)]

/-- The squared cosine and all pole-cancelling factors retain their signs. -/
theorem spectralABLExceptionalCorrected_re_nonneg (a : ℝ) (A : ℕ) (t : ℝ) :
    0 ≤ (spectralABLExceptionalCorrected a A (t : ℂ)).re := by
  rw [spectralABLExceptionalCorrected_real, spectralABLExceptionalWindow_real,
    ← Complex.ofReal_div, Complex.ofReal_re]
  exact div_nonneg (spectralABLExceptionalWindowReal_nonneg a A t) (Real.cosh_pos _).le

theorem spectralABLExceptionalCorrected_norm_real (a : ℝ) (A : ℕ) (t : ℝ) :
    ‖spectralABLExceptionalCorrected a A (t : ℂ)‖ =
      spectralABLExceptionalWindowReal a A t / Real.cosh (Real.pi * t) := by
  rw [spectralABLExceptionalCorrected_real, spectralABLExceptionalWindow_real,
    ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (spectralABLExceptionalWindowReal_nonneg a A t)
      (Real.cosh_pos _).le)]

/-- A uniform principal-axis majorant preserves the complete exceptional window. -/
theorem spectralABLExceptionalWindowReal_le_one (a : ℝ) (A : ℕ) (t : ℝ) :
    spectralABLExceptionalWindowReal a A t ≤ spectralABLExceptionalWindowReal 1 A t := by
  unfold spectralABLExceptionalWindowReal
  simp only [Real.log_one, mul_zero, Real.cos_zero, mul_one]
  have hc : (2 * Real.cos (2 * t * Real.log a)) ^ 2 ≤ (2 : ℝ) ^ 2 := by
    have h := Real.abs_cos_le_one (2 * t * Real.log a)
    have hlo := (abs_le.mp h).1
    have hhi := (abs_le.mp h).2
    nlinarith [sq_nonneg (Real.cos (2 * t * Real.log a))]
  apply mul_le_mul_of_nonneg_right
  · exact div_le_div_of_nonneg_right hc (by positivity)
  · exact Finset.prod_nonneg (fun _ _ => by positivity)

theorem spectralABLExceptionalCorrected_norm_le_one (a : ℝ) (A : ℕ) (t : ℝ) :
    ‖spectralABLExceptionalCorrected a A (t : ℂ)‖ ≤
      ‖spectralABLExceptionalCorrected 1 A (t : ℂ)‖ := by
  rw [spectralABLExceptionalCorrected_norm_real, spectralABLExceptionalCorrected_norm_real]
  exact div_le_div_of_nonneg_right (spectralABLExceptionalWindowReal_le_one a A t)
    (Real.cosh_pos _).le

end
end ArtinMatthews
