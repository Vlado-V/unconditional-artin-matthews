module

public import ArtinMatthews.SpectralSearsTitchmarsh
public import ArtinMatthews.SpectralJForwardRealWeight
public import ArtinMatthews.SpectralJGaussianCompletedCoefficient


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem spectralJForwardTransform_inverse (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioi (0 : ℝ)) :
    EqOn f (fun x =>
      spectralJWeightedSynthesis (fun r : ℝ => spectralJForwardSpectralWeight f (r : ℂ)) x +
        spectralJOddSynthesis f x) (Ioi (0 : ℝ)) := by
  let H : ℝ → ℂ := fun r => spectralJForwardSpectralWeight f (r : ℂ)
  apply spectralJ_reconstruction_of_completed_analysis f H hf hc hs
    (spectralJForwardSpectralWeight_real_contDiff f hf.continuous hc hs)
    (spectralJForwardSpectralWeight_real_directRapid f hf hc hs)
    (spectralJForwardSpectralWeight_weber_integrable f hf hc hs)
  obtain ⟨hG, hA⟩ := spectralJGaussianTail_normalized_completed_analysis f hf hc hs
  have hrem : spectralJGaussianRemainder f = fun y : ℝ =>
      (1 / (Real.sqrt (8 * Real.pi) : ℂ)) *
        spectralJGaussianTail (spectralJGaussianTransform f) y := by
    funext y
    simp only [spectralJGaussianRemainder, Complex.ofReal_div, Complex.ofReal_one]
  rw [hrem]
  refine ⟨hG, hA.trans ?_⟩
  filter_upwards [spectralKLPositiveWeightMeasure_ae_pos spectralKLPlancherelWeight] with r hr
  exact (spectralJForwardSpectralWeight_real_eq_weyl f hr).symm

theorem spectralJForwardTransform_inverse_apply (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioi (0 : ℝ)) {x : ℝ} (hx : 0 < x) :
    f x =
      spectralJWeightedSynthesis (fun r : ℝ => spectralJForwardSpectralWeight f (r : ℂ)) x +
        spectralJOddSynthesis f x :=
  spectralJForwardTransform_inverse f hf hc hs hx

end
end ArtinMatthews
