module

public import ArtinMatthews.SpectralKLTestSynthesisLinear


set_option backward.privateInPublic true
@[expose] public section

/-! The actual KL synthesis extended isometrically to the full weighted
spectral L2 space. Dense range in the physical space is not asserted here. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace ArtinMatthews

def spectralKLCompletedSynthesis : Lp ℂ 2 spectralKLSpectralMeasure →ₗᵢ[ℂ] Lp ℂ 2 spectralKLPhysicalMeasure :=
  spectralKLTestSynthesisLinear.extendOfIsometry spectralKLTestToLp_denseRange spectralKLTestSynthesis_norm

theorem spectralKLCompletedSynthesis_norm (u : Lp ℂ 2 spectralKLSpectralMeasure) :
    ‖spectralKLCompletedSynthesis u‖ = ‖u‖ := spectralKLCompletedSynthesis.norm_map u

theorem spectralKLCompletedSynthesis_test (g : spectralKLTestSubmodule) :
    spectralKLCompletedSynthesis (spectralKLTestToLp g) = spectralKLTestSynthesis g :=
  LinearMap.extendOfIsometry_eq _ spectralKLTestToLp_denseRange spectralKLTestSynthesis_norm g

theorem spectralKLCompletedSynthesis_test_ae (g : spectralKLTestSubmodule) :
    spectralKLCompletedSynthesis (spectralKLTestToLp g) =ᵐ[spectralKLPhysicalMeasure]
      spectralKLWeightedSynthesis g := by
  rw [spectralKLCompletedSynthesis_test]
  exact spectralKLTestSynthesis_coe g

theorem spectralKLCompletedSynthesis_injective : Function.Injective spectralKLCompletedSynthesis :=
  spectralKLCompletedSynthesis.injective

theorem spectralKLCompletedSynthesis_unique
    (T : Lp ℂ 2 spectralKLSpectralMeasure →ₗᵢ[ℂ] Lp ℂ 2 spectralKLPhysicalMeasure)
    (hT : ∀ g : spectralKLTestSubmodule, T (spectralKLTestToLp g) = spectralKLTestSynthesis g) :
    spectralKLCompletedSynthesis = T := by
  apply LinearMap.extendOfIsometry_unique _ spectralKLTestToLp_denseRange spectralKLTestSynthesis_norm T
  apply LinearMap.ext
  intro g
  exact hT g

end ArtinMatthews
