module

public import ArtinMatthews.SpectralKLInverseIAnalytic


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory
open scoped ContDiff
noncomputable section

theorem spectral_horizontal_shift_of_power_bound (F : ℂ → ℂ) (x C : ℝ) (hx : 0 < x) (hC : 0 ≤ C)
    (hhol : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 3 / 4 → DifferentiableAt ℂ F z)
    (hbound : ∀ t y : ℝ, 0 ≤ y → y ≤ 3 / 4 →
      ‖F ((t : ℂ) + (y : ℂ) * Complex.I)‖ ≤ C * Real.exp x * x ^ y / (1 + t ^ 2)) :
    (∫ t : ℝ, F (t : ℂ)) = ∫ t : ℝ, F ((t : ℂ) + (3 / 4 : ℂ) * Complex.I) := by
  have hb (t y : ℝ) (hy0 : 0 ≤ y) (hyB : y ≤ 3 / 4) :
      ‖F ((t : ℂ) + (y : ℂ) * Complex.I)‖ ≤
        (C * Real.exp x * (1 + x ^ (3 / 4 : ℝ))) * SourcePhysical.sourceContourHeightWeight t := by
    calc
      _ ≤ C * Real.exp x * x ^ y / (1 + t ^ 2) := hbound t y hy0 hyB
      _ ≤ (C * Real.exp x * (1 + x ^ (3 / 4 : ℝ))) / (1 + t ^ 2) := by
        gcongr
        exact spectral_positive_strip_power_bound hx hy0 hyB
      _ = _ := by rw [SourcePhysical.sourceContourHeightWeight, div_eq_mul_inv]
  simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using
    spectral_horizontal_integral_eq_of_heightWeight F (by norm_num) hhol hb

theorem spectralKLInverseIIntegrand_shift (h : ℂ → ℂ) (g : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ))
    (hh : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 3 / 4 → DifferentiableAt ℂ h z)
    (H : ℝ) (hH : 0 ≤ H)
    (hbound : ∀ t y : ℝ, 0 ≤ y → y ≤ 3 / 4 →
      ‖h ((t : ℂ) + (y : ℂ) * Complex.I)‖ ≤ H * (1 + t ^ 2))
    {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ, spectralKLInverseIIntegrand h g x (t : ℂ)) =
      ∫ t : ℝ, spectralKLInverseIIntegrand h g x ((t : ℂ) + (3 / 4 : ℂ) * Complex.I) := by
  obtain ⟨C, hC, henv⟩ := spectralKLInverseIIntegrand_strip_bound h g hg hc hp H hH hbound
  let F : ℂ → ℂ := spectralKLInverseIIntegrand h g x
  have hhol : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 3 / 4 → DifferentiableAt ℂ F z := by
    intro z hz0 hzB
    exact spectralKLInverseIIntegrand_differentiableAt h g hg.continuous hc hp hx
      (by linarith) (hh z hz0 hzB)
  have hb : ∀ t y : ℝ, 0 ≤ y → y ≤ 3 / 4 →
      ‖F ((t : ℂ) + (y : ℂ) * Complex.I)‖ ≤ C * Real.exp x * x ^ y / (1 + t ^ 2) :=
    fun t y hy0 hyB => henv t y x hy0 hyB hx
  exact spectral_horizontal_shift_of_power_bound F x C hx hC hhol hb

end
end ArtinMatthews
