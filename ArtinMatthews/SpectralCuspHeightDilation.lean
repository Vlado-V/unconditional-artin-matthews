module

public import ArtinMatthews.SpectralKLPhysicalDilation
public import ArtinMatthews.SpectralCuspDiagonalFourierIntegral


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory
noncomputable section

/-- Exact cancellation of the two square-root factors against the width and height density. -/
theorem cuspFourierHeightPairing_scaled_integrand {y w : ℝ}
    (hy : 0 < y) (hw : 0 < w) (a b : ℝ) :
    w * ((Real.sqrt (y / w) * a) * (Real.sqrt (y / w) * b) / y ^ 2) = a * b / y := by
  have hs : Real.sqrt (y / w) ^ 2 = y / w := Real.sq_sqrt (div_nonneg hy.le hw.le)
  calc
    _ = w * (Real.sqrt (y / w) ^ 2 * a * b / y ^ 2) := by ring
    _ = _ := by
      rw [hs]
      field_simp [hy.ne', hw.ne']

/-- The literal rescaled cusp height pairing is the physical dx/x pairing. -/
theorem cuspFourierHeightPairing_dilation (q w : ℝ) (hq : 0 < q) (hw : 0 < w)
    (f g : ℝ → ℝ) :
    w * cuspFourierHeightPairing
      (fun y => Real.sqrt (y / w) * f ((q / w) * y))
      (fun y => Real.sqrt (y / w) * g ((q / w) * y)) =
        ∫ x in Ioi (0 : ℝ), f x * g x / x := by
  calc
    _ = ∫ y in Ioi (0 : ℝ), f (y / (w / q)) * g (y / (w / q)) / y := by
      unfold cuspFourierHeightPairing
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      change w * ((Real.sqrt (y / w) * f ((q / w) * y)) *
        (Real.sqrt (y / w) * g ((q / w) * y)) / y ^ 2) =
          f (y / (w / q)) * g (y / (w / q)) / y
      have ha : y / (w / q) = (q / w) * y := by field_simp [hq.ne', hw.ne']
      rw [ha]
      exact cuspFourierHeightPairing_scaled_integrand hy hw _ _
    _ = _ := spectralKLPhysical_dilation_real_integral (fun x => f x * g x) (div_pos hw hq)

end
end ArtinMatthews
