module

public import ArtinMatthews.SpectralJSourceAbsolute
public import ArtinMatthews.SpectralJRegularizedNativeTerms
public import ArtinMatthews.SpectralNativeHermitian


set_option backward.privateInPublic true
@[expose] public section

/-! Each actual regularized energy test is absolutely summable in the native source expansion. -/
namespace ArtinMatthews
open Set MeasureTheory
open scoped ContDiff MatrixGroups
noncomputable section

theorem gamma0JRegularizedSource_absolute (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (L : ℝ) (hL : 0 ≤ L) :
    Summable (fun i => ‖gamma0BareCuspidalTerm (r * s)
      (spectralJRegularizedEnergyTest f hf hc hp L hL) 1 (gamma0CuspOneOver s) Y hY m n hm hn i‖) ∧
    IntegrableOn (gamma0BareContinuousRhoIntegrand (r * s)
      (spectralJRegularizedEnergyTest f hf hc hp L hL) 1 (gamma0CuspOneOver s) Y hY m n hm hn) (Ioi (0 : ℝ)) := by
  obtain ⟨hC, hI⟩ := gamma0JSource_absolute f hf hc hp r s hcop Y hY m n hm hn
  constructor
  · apply hC.of_nonneg_of_le (fun _ => norm_nonneg _)
    intro i
    rw [gamma0JRegularized_cuspidal_term]
    exact spectralJRegularizationMultiplier_mul_norm_le hL
      (gamma0AllHeightGradientSpectralValue_nonneg (r * s) i) _
  · apply hI.norm.mono'
      (gamma0BareContinuousRhoIntegrand_aestronglyMeasurable (r * s)
        (spectralJRegularizedEnergyTest f hf hc hp L hL) 1 (gamma0CuspOneOver s) Y hY m n hm hn)
    filter_upwards with t
    rw [gamma0JRegularized_continuous_term]
    exact spectralJRegularizationMultiplier_mul_norm_le hL (by positivity) _

theorem gamma0JRegularizedSource_absolute_swapped (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (L : ℝ) (hL : 0 ≤ L) :
    Summable (fun i => ‖gamma0BareCuspidalTerm (r * s)
      (spectralJRegularizedEnergyTest f hf hc hp L hL) (gamma0CuspOneOver s) 1 Y hY n m hn hm i‖) ∧
    IntegrableOn (gamma0BareContinuousRhoIntegrand (r * s)
      (spectralJRegularizedEnergyTest f hf hc hp L hL) (gamma0CuspOneOver s) 1 Y hY n m hn hm) (Ioi (0 : ℝ)) := by
  obtain ⟨hC, hI⟩ := gamma0JRegularizedSource_absolute f hf hc hp r s hcop Y hY m n hm hn L hL
  exact gamma0BareSource_absolute_swap (r * s) _ 1 (gamma0CuspOneOver s) Y hY m n hm hn hC hI

end
end ArtinMatthews
