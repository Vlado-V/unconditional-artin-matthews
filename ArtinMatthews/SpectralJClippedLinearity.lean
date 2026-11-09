module

public import ArtinMatthews.SpectralJClippedEnergyTest
public import ArtinMatthews.SpectralJSourceTestSplit


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set Complex
open scoped ContDiff ComplexConjugate
noncomputable section

theorem spectralJClippedWeight_parts
    (f : ℝ → ℂ) (hf : Continuous f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ)) (l : ℝ) :
    spectralJClippedWeight f l =
      spectralJClippedWeight (spectralJRealTest f) l +
        I * spectralJClippedWeight (spectralJImagTest f) l := by
  simp only [spectralJClippedWeight, spectralJForwardTransform_parts f hf hc hp]
  ring

end
end ArtinMatthews
