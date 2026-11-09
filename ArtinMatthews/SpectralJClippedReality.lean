module

public import ArtinMatthews.SpectralJNativeSymbols
public import ArtinMatthews.SpectralJRegularizedReality


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set
open scoped ContDiff ComplexConjugate
noncomputable section

theorem spectralJClippedEnergyTest_real (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (hReal : ∀ x : ℝ, conj (f x) = f x) (l : Ici (0 : ℝ)) :
    star (spectralJClippedEnergyTest f hf hc hp l) = spectralJClippedEnergyTest f hf hc hp l := by
  let q : ℝ := max (3 / 16 : ℝ) (l : ℝ)
  have hq : 0 < q := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 16) (le_max_left _ _)
  let qsub : Ici (0 : ℝ) := ⟨q, hq.le⟩
  have hr := spectralJRegularizedEnergyTest_real f hf hc hp hReal 1 (by norm_num) qsub
  rw [spectralJRegularizedEnergyTest_pos f hf hc hp 1 (by norm_num) qsub hq,
    star_mul, show star (spectralJRegularizationMultiplier 1 q : ℂ) =
      (spectralJRegularizationMultiplier 1 q : ℂ) from Complex.conj_ofReal _] at hr
  have hqmul : 0 < spectralJRegularizationMultiplier 1 q := by
    unfold spectralJRegularizationMultiplier
    have he : Real.exp (-(1 * q)) < 1 := Real.exp_lt_one_iff.mpr (by linarith only [hq])
    linarith
  have hr' : (spectralJRegularizationMultiplier 1 q : ℂ) *
      star (spectralJForwardSpectralWeight f (spectralSourceParameter q)) =
      (spectralJRegularizationMultiplier 1 q : ℂ) *
        spectralJForwardSpectralWeight f (spectralSourceParameter q) := by
    simpa only [mul_comm] using hr
  have he := mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hqmul.ne') hr'
  rw [spectralJClippedEnergyTest_apply, spectralJClippedWeight_native_clamp]
  exact he

end
end ArtinMatthews
