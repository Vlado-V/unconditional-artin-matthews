module

public import ArtinMatthews.SpectralJRegularizedIntegrability
public import Mathlib.MeasureTheory.Integral.DominatedConvergence


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

open Set MeasureTheory Filter
open scoped ContDiff Topology
noncomputable section

theorem spectralJRegularizedWeight_real_tendsto (f : ℝ → ℂ) (t : ℝ) :
    Tendsto (fun L : ℝ => spectralJRegularizedWeight f L (t : ℂ)) atTop
      (𝓝 (spectralJForwardSpectralWeight f (t : ℂ))) := by
  have hq := (Complex.continuous_ofReal.tendsto 1).comp
    (spectralJRegularizationMultiplier_tendsto (l := 1 / 4 + t ^ 2) (by positivity))
  have h := hq.mul_const (spectralJForwardSpectralWeight f (t : ℂ))
  simpa only [spectralJRegularizedWeight_real_eq_factor, Function.comp_def,
    Complex.ofReal_one, one_mul] using h

theorem spectralJRegularizedBareKernel_tendsto (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (m n : ℤ) {X : ℝ} (hX : 0 < X) :
    Tendsto (fun L : ℝ => spectralABLBareKernel (spectralJRegularizedWeight f L) m n X) atTop
      (𝓝 (spectralABLBareKernel (spectralJForwardSpectralWeight f) m n X)) := by
  have hnorm : Integrable (fun t : ℝ => ‖spectralJForwardSpectralWeight f (t : ℂ)‖)
      spectralKLSpectralMeasure := by
    simpa using spectralJForwardSpectralWeight_weighted_integrable f hf hc hp 0 le_rfl
  have hH : Integrable (fun t : ℝ => spectralJForwardSpectralWeight f (t : ℂ))
      spectralKLSpectralMeasure :=
    hnorm.mono' (spectralJForwardSpectralWeight_real_contDiff f hf.continuous hc hp).continuous.aestronglyMeasurable
      (ae_of_all _ fun _ => le_rfl)
  have hi := spectralABLBareKernel_integrable _ hH m n hX
  unfold spectralABLBareKernel
  apply tendsto_integral_filter_of_dominated_convergence
    (fun t : ℝ => ‖spectralWeylIntegerSignMultiplier m n t X *
      spectralJForwardSpectralWeight f (t : ℂ)‖)
  · apply Eventually.of_forall
    intro L
    exact (spectralWeylIntegerSignMultiplier_measurable m n X).aestronglyMeasurable.mul
      (spectralJRegularizedWeight_real_contDiff f hf.continuous hc hp L).continuous.aestronglyMeasurable
  · apply (eventually_ge_atTop (0 : ℝ)).mono
    intro L hL
    exact ae_of_all _ fun t => by
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (spectralJRegularizedWeight_real_norm_le f L hL t) (norm_nonneg _)
  · exact hi.norm
  · exact ae_of_all _ fun t => tendsto_const_nhds.mul (spectralJRegularizedWeight_real_tendsto f t)

end
end ArtinMatthews
