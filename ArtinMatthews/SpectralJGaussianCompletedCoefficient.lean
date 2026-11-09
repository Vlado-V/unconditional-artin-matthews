module

public import ArtinMatthews.SpectralJGaussianRealCoefficient
public import ArtinMatthews.SpectralJGaussianTailAnalysis


set_option backward.privateInPublic true
@[expose] public section

/-! The normalized tail has the actual native coefficient in completed KL space. -/
namespace ArtinMatthews
open MeasureTheory Set Filter
open scoped ContDiff
noncomputable section

theorem spectralJGaussianTail_normalized_completed_analysis (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (hpos : tsupport f ⊆ Ioi (0 : ℝ)) :
    let G := fun y : ℝ => (1 / (Real.sqrt (8 * Real.pi) : ℂ)) *
      spectralJGaussianTail (spectralJGaussianTransform f) y
    ∃ hG : MemLp G 2 spectralKLPhysicalMeasure,
      spectralKLAnalysis (hG.toLp G) =ᵐ[spectralKLSpectralMeasure] fun r : ℝ =>
        (∫ x : ℝ in Ioi 0, f x * spectralWeylJMultiplier r x) /
          (4 * (Real.cosh (Real.pi * r) : ℂ)) := by
  let F := spectralJGaussianTransform f
  let G := spectralJGaussianTail F
  let c : ℂ := 1 / (Real.sqrt (8 * Real.pi) : ℂ)
  have hfi : IntegrableOn f (Ioi (0 : ℝ)) :=
    (hf.continuous.integrable_of_hasCompactSupport hfc).integrableOn
  have hFm := (spectralJGaussianTransform_continuous f hf.continuous hfi).measurable
  have hFi := spectralJGaussianTransform_integrableOn_tail f hf hfc hpos
  have hG : MemLp G 2 spectralKLPhysicalMeasure := spectralJGaussianTail_memLp F hFm hFi
  refine ⟨hG.const_smul c, ?_⟩
  change spectralKLAnalysis ((hG.const_smul c).toLp (c • G)) =ᵐ[spectralKLSpectralMeasure] _
  rw [MemLp.toLp_const_smul c hG, map_smul]
  filter_upwards [Lp.coeFn_smul c (spectralKLAnalysis (hG.toLp G)),
    spectralJGaussianTail_completed_analysis F hFm hFi,
    spectralKLPositiveWeightMeasure_ae_pos spectralKLPlancherelWeight] with r hscale hraw hr
  rw [hscale]
  change c * spectralKLAnalysis (hG.toLp G) r = _
  rw [hraw, spectralJGaussianTail_analysisIntegral_eq]
  have he := spectralJGaussianTail_real_coefficient f hf hfc hpos r hr
  rw [← he]
  dsimp only [c]
  ring

end
end ArtinMatthews
