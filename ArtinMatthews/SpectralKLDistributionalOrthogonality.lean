module

public import ArtinMatthews.SpectralKLTestLimit


set_option backward.privateInPublic true
@[expose] public section

/-! Positive-spectrum distributional KL orthogonality for a smooth spectral
test on the open positive half-line. This is not an inversion, Plancherel,
or completeness assertion. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein
open scoped Topology ContDiff

namespace ArtinMatthews

theorem schlafliBesselK_product_mellin_smooth_test_limit (t : ℝ) (ht : 0 < t)
    (f : ℝ → ℂ) (hf : ContDiffOn ℝ ∞ f (Ioi (0 : ℝ)))
    (hfc : HasCompactSupport f) (hpos : tsupport f ⊆ Ioi (0 : ℝ)) :
    Tendsto (fun ε : ℝ => ∫ v in Ioi (0 : ℝ), f v *
      (∫ x in Ioi (0 : ℝ), (x : ℂ)^((ε : ℂ)-1)*
        schlafliBesselK ((t : ℂ)*Complex.I) x*schlafliBesselK ((v : ℂ)*Complex.I) x))
      (𝓝[>] (0 : ℝ)) (𝓝 ((Real.pi^2/(2*t*Real.sinh (Real.pi*t)) : ℝ) • f t)) := by
  exact schlafliBesselK_product_mellin_test_limit t ht f
    (hf.continuousOn.continuous_of_tsupport_subset isOpen_Ioi hpos) hfc hpos

end ArtinMatthews
