module

public import ArtinMatthews.SpectralJRegularizedEnergyTest
public import ArtinMatthews.SpectralJForwardReality
public import ArtinMatthews.SpectralABLMultiplierReality


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

open Complex Set
open scoped ContDiff ComplexConjugate
noncomputable section

theorem spectralJRegularizerPrimitive_conj (L : ℝ) (w : ℂ) :
    conj (spectralJRegularizerPrimitive L w) = spectralJRegularizerPrimitive L (conj w) := by
  rw [spectralJRegularizerPrimitive_integral, spectralJRegularizerPrimitive_integral,
    ← intervalIntegral.intervalIntegral_conj]
  apply intervalIntegral.integral_congr
  intro s _
  change conj (Complex.exp (-(s : ℂ) * w)) = Complex.exp (-(s : ℂ) * conj w)
  rw [← Complex.exp_conj]
  simp only [map_mul, map_neg, Complex.conj_ofReal]

theorem spectralJRegularizedWeight_conj (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (hReal : ∀ x : ℝ, conj (f x) = f x) (L : ℝ) (z : ℂ) :
    conj (spectralJRegularizedWeight f L z) = spectralJRegularizedWeight f L (conj z) := by
  have hC := spectralABLCoshCancellation_conj z
  change conj (spectralABLCoshCancellation z) = spectralABLCoshCancellation (conj z) at hC
  simp only [spectralJRegularizedWeight, map_mul, Complex.conj_ofReal,
    spectralJForwardTransform_conj f hf hc hp hReal z, hC,
    spectralJRegularizerPrimitive_conj, map_add, map_pow, map_div₀, map_ofNat, map_one]

theorem spectralJRegularizedEnergyTest_real (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (hReal : ∀ x : ℝ, conj (f x) = f x) (L : ℝ) (hL : 0 ≤ L)
    (l : Ici (0 : ℝ)) :
    star (spectralJRegularizedEnergyTest f hf hc hp L hL l) =
      spectralJRegularizedEnergyTest f hf hc hp L hL l := by
  rw [spectralJRegularizedEnergyTest_apply]
  change conj (spectralJRegularizedWeight f L (spectralSourceParameter l)) = _
  rw [spectralJRegularizedWeight_conj f hf.continuous hc hp hReal L]
  by_cases hl : 1 / 4 ≤ (l : ℝ)
  · rw [spectralSourceParameter_principal l hl, Complex.conj_ofReal]
  · have hparam : spectralSourceParameter l =
        (Real.sqrt (1 / 4 - (l : ℝ)) : ℂ) * I := by
      rw [spectralSourceParameter, Real.sqrt_eq_zero_of_nonpos (by linarith)]
      simp only [Complex.ofReal_zero, zero_add]
    rw [hparam, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg,
      spectralJRegularizedWeight_even]

end
end ArtinMatthews
