module

public import ArtinMatthews.SpectralJClippedEnergyTest
public import ArtinMatthews.SpectralJNativeAmplitudes
public import ArtinMatthews.SpectralJForwardWeightReality


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set
open scoped ContDiff MatrixGroups
noncomputable section

theorem spectralJClippedWeight_native_clamp (f : ℝ → ℂ) (l : ℝ) :
    spectralJClippedWeight f l =
      spectralJForwardSpectralWeight f (spectralSourceParameter (max (3 / 16 : ℝ) l)) := by
  have h := spectralJClippedWeight_native f (max (3 / 16 : ℝ) l) (le_max_left _ _)
  simpa only [spectralJClippedWeight, max_eq_right (le_max_left (3 / 16 : ℝ) l)] using h

theorem spectralJClippedEnergyTest_continuous_symbol (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) (t : ℝ) :
    spectralContinuousTestSymbol (spectralJClippedEnergyTest f hf hc hp) t =
      spectralJForwardSpectralWeight f (t : ℂ) := by
  change spectralJClippedWeight f (1 / 4 + t ^ 2) = _
  rw [spectralJClippedWeight_native f _ (by nlinarith only [sq_nonneg t]),
    spectralSourceParameter_frequency]
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht), Complex.ofReal_neg, spectralJForwardSpectralWeight_even]

theorem gamma0JClipped_principal_symbol (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (N : ℕ) [NeZero N] (i : Gamma0HeatPrincipalCuspidalIndex N) :
    gamma0CuspidalTestSymbol N (spectralJClippedEnergyTest f hf hc hp) i.val =
      spectralJForwardSpectralWeight f (gamma0CuspPrincipalParameter N i.val : ℂ) := by
  change spectralJClippedWeight f (gamma0AllHeightGradientSpectralValue N i.val) = _
  rw [spectralJClippedWeight_native f _ (by linarith only [i.property]),
    spectralSourceParameter_principal _ i.property]
  rfl

end
end ArtinMatthews
