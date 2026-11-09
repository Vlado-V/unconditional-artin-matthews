module

public import ArtinMatthews.SpectralJRegularizedEnergyTest
public import ArtinMatthews.SpectralJForwardWeightReality
public import ArtinMatthews.SpectralHeatKernelLimit


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

open Set MeasureTheory Filter
open scoped ContDiff Topology
noncomputable section

theorem spectralJRegularizedWeight_real_eq_factor (f : ℝ → ℂ) (L t : ℝ) :
    spectralJRegularizedWeight f L (t : ℂ) =
      (spectralJRegularizationMultiplier L (1 / 4 + t ^ 2) : ℂ) *
        spectralJForwardSpectralWeight f (t : ℂ) := by
  have h := spectralJRegularizedWeight_source_pos f L (1 / 4 + t ^ 2) (by positivity)
  rw [spectralSourceParameter_frequency] at h
  by_cases ht : 0 ≤ t
  · simpa only [abs_of_nonneg ht, spectralJRegularizationMultiplier] using h
  · rw [abs_of_neg (lt_of_not_ge ht), Complex.ofReal_neg,
      spectralJRegularizedWeight_even, spectralJForwardSpectralWeight_even] at h
    exact h

theorem spectralJRegularizedWeight_real_norm_le (f : ℝ → ℂ)
    (L : ℝ) (hL : 0 ≤ L) (t : ℝ) :
    ‖spectralJRegularizedWeight f L (t : ℂ)‖ ≤ ‖spectralJForwardSpectralWeight f (t : ℂ)‖ := by
  rw [spectralJRegularizedWeight_real_eq_factor, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (spectralJRegularizationMultiplier_bounds hL (by positivity)).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (spectralJRegularizationMultiplier_bounds hL (by positivity)).2

theorem spectralJRegularizedWeight_spectral_integrable (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (L : ℝ) (hL : 0 ≤ L) :
    Integrable (fun t : ℝ => spectralJRegularizedWeight f L (t : ℂ)) spectralKLSpectralMeasure := by
  have hnorm : Integrable (fun t : ℝ => ‖spectralJForwardSpectralWeight f (t : ℂ)‖)
      spectralKLSpectralMeasure := by
    simpa using spectralJForwardSpectralWeight_weighted_integrable f hf hc hp 0 le_rfl
  exact hnorm.mono' (spectralJRegularizedWeight_real_contDiff f hf.continuous hc hp L).continuous.aestronglyMeasurable
    (ae_of_all _ fun t => spectralJRegularizedWeight_real_norm_le f L hL t)

theorem spectralJRegularizedHeatKernel_tendsto_bare (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (L : ℝ) (hL : 0 ≤ L) (m n : ℤ) {X : ℝ} (hX : 0 < X) :
    Tendsto (fun R : ℝ => spectralABLHeatKernel (spectralJRegularizedWeight f L) R m n X) atTop
      (𝓝 (spectralABLBareKernel (spectralJRegularizedWeight f L) m n X)) :=
  spectralABLHeatKernel_tendsto_bare _ (spectralJRegularizedWeight_spectral_integrable f hf hc hp L hL) m n hX

end
end ArtinMatthews
