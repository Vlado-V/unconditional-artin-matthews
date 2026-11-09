module

public import ArtinMatthews.SpectralMixedCuspBesselPairing


set_option backward.privateInPublic true
@[expose] public section

/-! Exact true-width transport of the height budget. Both scaled lower
supports and both square-root height factors are needed to cancel the
cube of the normalized modulus in the compact orbital bound. -/

noncomputable section
open MeasureTheory Set

namespace ArtinMatthews

theorem spectralKLHeightBaseTest_width (w : ℝ) (hw : 0 < w) (ρ : ℝ → ℝ) (y : ℝ) :
    spectralKLHeightBaseTest (fun x => ρ (w*x)) y =
      (Real.sqrt w : ℂ)*spectralKLHeightBaseTest ρ (w*y) := by
  by_cases hy : y = 0
  · simp [hy,spectralKLHeightBaseTest]
  unfold spectralKLHeightBaseTest
  simp only [← Complex.ofReal_div,← Complex.ofReal_mul]
  congr 1
  rw [Real.sqrt_mul hw.le]
  field_simp [hw.ne',hy]
  linear_combination -(ρ (w*y)*Real.sqrt y)*Real.sq_sqrt hw.le

theorem spectralKLHeightBaseTest_width_norm (w : ℝ) (hw : 0 < w) (ρ : ℝ → ℝ) (y : ℝ) :
    ‖spectralKLHeightBaseTest (fun x => ρ (w*x)) y‖ =
      Real.sqrt w*‖spectralKLHeightBaseTest ρ (w*y)‖ := by
  rw [spectralKLHeightBaseTest_width w hw,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]

theorem spectralKLHeightBaseTest_width_norm_integral (w : ℝ) (hw : 0 < w) (ρ : ℝ → ℝ) :
    (∫ y : ℝ, ‖spectralKLHeightBaseTest (fun x => ρ (w*x)) y‖ ∂spectralKLPhysicalMeasure) =
      Real.sqrt w*(∫ y : ℝ, ‖spectralKLHeightBaseTest ρ y‖ ∂spectralKLPhysicalMeasure) := by
  have h := spectralKLPhysical_measure_dilation_integral (fun y : ℝ => (‖spectralKLHeightBaseTest ρ y‖ : ℂ)) hw
  simp only [integral_complex_ofReal] at h
  simp_rw [spectralKLHeightBaseTest_width_norm w hw]
  rw [integral_const_mul,← Complex.ofReal_injective h]

theorem spectralWeylCompactHeightBudget_width {w v A B : ℝ}
    (hw : 0 < w) (hv : 0 < v) (hA : 0 < A) (hB : 0 < B) (M : ℝ) (ρ : ℝ → ℝ) :
    spectralWeylCompactHeightBudget (A/w) (B/v) (Real.sqrt v*M) (fun y => ρ (w*y)) =
      (Real.sqrt w*Real.sqrt v)^3*spectralWeylCompactHeightBudget A B M ρ := by
  unfold spectralWeylCompactHeightBudget
  rw [spectralKLHeightBaseTest_width_norm_integral w hw,mul_pow,pow_succ (Real.sqrt w) 2,
    pow_succ (Real.sqrt v) 2,Real.sq_sqrt hw.le,Real.sq_sqrt hv.le]
  field_simp [hw.ne',hv.ne',hA.ne',hB.ne']

end ArtinMatthews
