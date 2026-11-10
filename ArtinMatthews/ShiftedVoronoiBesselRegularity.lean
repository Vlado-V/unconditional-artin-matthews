module

public import ArtinMatthews.ShiftedVoronoiBesselDuality
public import ArtinMatthews.ShiftedVoronoiBesselBounds


set_option backward.privateInPublic true
@[expose] public section

/-!
# Continuity of the Bessel transform of a compact source

Uniform compact support in the integration variable allows continuity to pass
through the integral. No decay or transform identity is assumed.
-/

noncomputable section
open MeasureTheory Set Complex

namespace ArtinMatthews

theorem continuous_besselZeroTransform (H : ℝ → ℂ) (hHc : Continuous H)
    (hHk : HasCompactSupport H) : Continuous (besselZeroTransform H) := by
  unfold besselZeroTransform
  rw [← continuousOn_univ]
  apply continuousOn_integral_of_compact_support (μ := volume.restrict (Ioi 0))
    hHk.isCompact
  · apply Continuous.continuousOn
    fun_prop
  · intro y x hy hx
    simp [image_eq_zero_of_notMem_tsupport hx]

end ArtinMatthews
