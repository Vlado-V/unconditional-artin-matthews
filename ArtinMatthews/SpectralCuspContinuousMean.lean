module

public import ArtinMatthews.SpectralCuspContinuousRepresentative
public import ArtinMatthews.SpectralGamma0EisensteinIntegralExchange


set_option backward.privateInPublic true
@[expose] public section

/-! Above the extension height the literal horizontal mean is the actual
horocycle integral. This small generic adapter avoids unfolding ambient L2. -/
noncomputable section
open Set MeasureTheory
namespace ArtinMatthews

theorem cuspContinuousPlaneExtension_mean (w Y : ℝ) (hw : 0≤w) (hY : 0<Y)
    (F : UpperHalfPlane → ℂ) (y : ℝ) (hy : Y<y) :
    cuspHorizontalMean w (cuspContinuousPlaneExtension Y hY F) y=
      (w:ℂ)⁻¹*(∫ x in (0:ℝ)..w, F (gamma0EisensteinHorizontalPoint y (hY.trans hy) x)) := by
  unfold cuspHorizontalMean
  rw [← intervalIntegral.integral_of_le hw]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  exact cuspContinuousPlaneExtension_at_upper Y hY F
    (gamma0EisensteinHorizontalPoint y (hY.trans hy) x) hy.le

end ArtinMatthews
