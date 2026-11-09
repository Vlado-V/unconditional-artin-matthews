module

public import ArtinMatthews.SpectralJRegularizationGap
public import ArtinMatthews.SpectralJClippedEnergyTest
public import ArtinMatthews.SpectralJRegularizedEnergyTest
public import ArtinMatthews.SpectralJNativeAmplitudes
public import ArtinMatthews.SpectralGamma0UniformGap
public import ArtinMatthews.SpectralInfinityResidualGap


set_option backward.privateInPublic true
@[expose] public section

/-! Exact regularized factors on every contributing native spectral term. -/
namespace ArtinMatthews
open Set
open scoped ContDiff MatrixGroups
noncomputable section

theorem spectralJRegularizedEnergyTest_above_gap (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (L : ℝ) (hL : 0 ≤ L) (l : Ici (0 : ℝ)) (hl : 3 / 16 ≤ (l : ℝ)) :
    spectralJRegularizedEnergyTest f hf hc hp L hL l =
      (spectralJRegularizationMultiplier L l : ℂ) * spectralJClippedEnergyTest f hf hc hp l := by
  rw [spectralJRegularizedEnergyTest_pos f hf hc hp L hL l
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 16) hl),
    spectralJClippedEnergyTest_apply, spectralJClippedWeight_native f l hl]

theorem gamma0JRegularized_cuspidal_term (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (N : ℕ) [NeZero N] (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (L : ℝ) (hL : 0 ≤ L)
    (i : Gamma0AllHeightSpectralIndex N) :
    gamma0BareCuspidalTerm N (spectralJRegularizedEnergyTest f hf hc hp L hL)
      r s Y hY m n hm hn i =
      (spectralJRegularizationMultiplier L (gamma0AllHeightGradientSpectralValue N i) : ℂ) *
        gamma0BareCuspidalTerm N (spectralJClippedEnergyTest f hf hc hp) r s Y hY m n hm hn i := by
  unfold gamma0BareCuspidalTerm gamma0CuspidalTestSymbol
  rw [spectralJRegularizedEnergyTest_above_gap f hf hc hp L hL _
    (gamma0AllHeightGradientSpectralValue_ge_three_sixteenths N i)]
  ring

theorem gamma0JRegularized_continuous_term (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (N : ℕ) [NeZero N] (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (L : ℝ) (hL : 0 ≤ L) (t : ℝ) :
    gamma0BareContinuousRhoIntegrand N (spectralJRegularizedEnergyTest f hf hc hp L hL)
      r s Y hY m n hm hn t =
      (spectralJRegularizationMultiplier L (1 / 4 + t ^ 2) : ℂ) *
        gamma0BareContinuousRhoIntegrand N (spectralJClippedEnergyTest f hf hc hp)
          r s Y hY m n hm hn t := by
  have hh := spectralJRegularizedEnergyTest_above_gap f hf hc hp L hL
    (spectralContinuousEnergyParameter t) (by
      change (3 / 16 : ℝ) ≤ 1 / 4 + t ^ 2
      nlinarith only [sq_nonneg t])
  unfold gamma0BareContinuousRhoIntegrand spectralContinuousTestSymbol
  change ((spectralJRegularizedEnergyTest f hf hc hp L hL (spectralContinuousEnergyParameter t)) /
      ((2 * Real.pi : ℝ) : ℂ)) * _ = _
  rw [hh]
  change (((spectralJRegularizationMultiplier L (1 / 4 + t ^ 2) : ℂ) *
      spectralJClippedEnergyTest f hf hc hp (spectralContinuousEnergyParameter t)) /
      ((2 * Real.pi : ℝ) : ℂ)) * _ =
    (spectralJRegularizationMultiplier L (1 / 4 + t ^ 2) : ℂ) *
      ((spectralJClippedEnergyTest f hf hc hp (spectralContinuousEnergyParameter t) /
        ((2 * Real.pi : ℝ) : ℂ)) * _)
  ring

theorem gamma0JRegularized_residual_term (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (N : ℕ) [NeZero N] (s : SL(2, ℤ))
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (L : ℝ) (hL : 0 ≤ L)
    (l : Ici (0 : ℝ)) (j : Fin (Module.finrank ℂ (gamma0ResidualEnergyEigenspace N l))) :
    gamma0BareResidualRhoTerm N (spectralJRegularizedEnergyTest f hf hc hp L hL)
      1 s m n hm hn l j =
      (spectralJRegularizationMultiplier L l : ℂ) *
        gamma0BareResidualRhoTerm N (spectralJClippedEnergyTest f hf hc hp)
          1 s m n hm hn l j := by
  by_cases hρ : gamma0ResidualABLSourceRho N l j 1 m hm = 0
  · simp only [gamma0BareResidualRhoTerm, hρ, mul_zero, zero_mul]
  · have hl := gamma0Infinity_residual_value_ge_three_sixteenths_of_rho N l j m hm hρ
    unfold gamma0BareResidualRhoTerm
    rw [spectralJRegularizedEnergyTest_above_gap f hf hc hp L hL l hl]
    ring

theorem gamma0JRegularized_cuspidal_error_le (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (N : ℕ) [NeZero N] (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (L : ℝ) (hL : 0 ≤ L)
    (i : Gamma0AllHeightSpectralIndex N) :
    ‖gamma0BareCuspidalTerm N (spectralJRegularizedEnergyTest f hf hc hp L hL)
        r s Y hY m n hm hn i -
      gamma0BareCuspidalTerm N (spectralJClippedEnergyTest f hf hc hp)
        r s Y hY m n hm hn i‖ ≤
      Real.exp (-(L * (3 / 16))) *
        ‖gamma0BareCuspidalTerm N (spectralJClippedEnergyTest f hf hc hp)
          r s Y hY m n hm hn i‖ := by
  rw [gamma0JRegularized_cuspidal_term]
  exact spectralJRegularizationMultiplier_mul_error_le hL
    (gamma0AllHeightGradientSpectralValue_ge_three_sixteenths N i) _

theorem gamma0JRegularized_continuous_error_le (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (N : ℕ) [NeZero N] (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (L : ℝ) (hL : 0 ≤ L) (t : ℝ) :
    ‖gamma0BareContinuousRhoIntegrand N (spectralJRegularizedEnergyTest f hf hc hp L hL)
        r s Y hY m n hm hn t -
      gamma0BareContinuousRhoIntegrand N (spectralJClippedEnergyTest f hf hc hp)
        r s Y hY m n hm hn t‖ ≤
      Real.exp (-(L * (3 / 16))) *
        ‖gamma0BareContinuousRhoIntegrand N (spectralJClippedEnergyTest f hf hc hp)
          r s Y hY m n hm hn t‖ := by
  rw [gamma0JRegularized_continuous_term]
  exact spectralJRegularizationMultiplier_mul_error_le hL
    (by nlinarith only [sq_nonneg t]) _

theorem gamma0JRegularized_residual_error_le (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (N : ℕ) [NeZero N] (s : SL(2, ℤ))
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (L : ℝ) (hL : 0 ≤ L)
    (l : Ici (0 : ℝ)) (j : Fin (Module.finrank ℂ (gamma0ResidualEnergyEigenspace N l))) :
    ‖gamma0BareResidualRhoTerm N (spectralJRegularizedEnergyTest f hf hc hp L hL)
        1 s m n hm hn l j -
      gamma0BareResidualRhoTerm N (spectralJClippedEnergyTest f hf hc hp)
        1 s m n hm hn l j‖ ≤
      Real.exp (-(L * (3 / 16))) *
        ‖gamma0BareResidualRhoTerm N (spectralJClippedEnergyTest f hf hc hp)
          1 s m n hm hn l j‖ := by
  by_cases hρ : gamma0ResidualABLSourceRho N l j 1 m hm = 0
  · simp only [gamma0BareResidualRhoTerm, hρ, mul_zero, zero_mul, sub_self, norm_zero, le_refl]
  · rw [gamma0JRegularized_residual_term]
    exact spectralJRegularizationMultiplier_mul_error_le hL
      (gamma0Infinity_residual_value_ge_three_sixteenths_of_rho N l j m hm hρ) _

end
end ArtinMatthews
