module

public import ArtinMatthews.SpectralJNativeSymbols
public import ArtinMatthews.SpectralJContinuousMass


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute convergence of the literal continuous source pairing. -/
namespace ArtinMatthews
open Set MeasureTheory
open scoped ContDiff MatrixGroups BigOperators
noncomputable section

theorem gamma0JClipped_continuous_absolute_of_densities
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (N : ℕ) [NeZero N] (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (hr : Integrable (fun t : ℝ => gamma0ContinuousPrincipalDensity N r Y hY m hm t /
      (1 + |t|) ^ 4) gamma0EisensteinSpectralMeasure)
    (hs : Integrable (fun t : ℝ => gamma0ContinuousPrincipalDensity N s Y hY n hn t /
      (1 + |t|) ^ 4) gamma0EisensteinSpectralMeasure) :
    IntegrableOn (gamma0BareContinuousRhoIntegrand N (spectralJClippedEnergyTest f hf hc hp)
      r s Y hY m n hm hn) (Ioi (0 : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := spectralJForwardTransform_real_rapid f hf hc hp 4
  have hc₀ : ENNReal.ofReal ((2 * Real.pi)⁻¹) ≠ 0 := by positivity
  have hr' : Integrable (fun t : ℝ => gamma0ContinuousPrincipalDensity N r Y hY m hm t /
      (1 + |t|) ^ 4) (volume.restrict (Ioi (0 : ℝ))) :=
    (integrable_smul_measure hc₀ ENNReal.ofReal_ne_top).mp hr
  have hs' : Integrable (fun t : ℝ => gamma0ContinuousPrincipalDensity N s Y hY n hn t /
      (1 + |t|) ^ 4) (volume.restrict (Ioi (0 : ℝ))) :=
    (integrable_smul_measure hc₀ ENNReal.ofReal_ne_top).mp hs
  have hmajor := (hr'.add hs').const_mul (C / 4)
  apply hmajor.mono'
    (gamma0BareContinuousRhoIntegrand_aestronglyMeasurable N
      (spectralJClippedEnergyTest f hf hc hp) r s Y hY m n hm hn)
  filter_upwards with t
  let P (j : Gamma0EisensteinCuspClasses N) :=
    gamma0PrimitiveFourierAmplitude N (gamma0EisensteinCuspClassRepresentative N j)
      r Y hY m hm (eisensteinCriticalPoint t)
  let Q (j : Gamma0EisensteinCuspClasses N) :=
    gamma0PrimitiveFourierAmplitude N (gamma0EisensteinCuspClassRepresentative N j)
      s Y hY n hn (eisensteinCriticalPoint t)
  let W := Real.cosh (Real.pi * t)
  have hW : 0 < W := Real.cosh_pos _
  have ha (j : Gamma0EisensteinCuspClasses N) :
      ‖gamma0BareEisensteinSourceCoefficient N j r Y hY m hm t‖ ≤ ‖P j‖ := by
    rw [gamma0BareEisensteinSourceCoefficient_half_amplitude, norm_mul]
    have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [hhalf]
    change (1 / 2 : ℝ) * ‖P j‖ ≤ ‖P j‖
    nlinarith only [norm_nonneg (P j)]
  have hb (j : Gamma0EisensteinCuspClasses N) :
      ‖gamma0BareEisensteinSourceCoefficient N j s Y hY n hn t‖ ≤ ‖Q j‖ := by
    rw [gamma0BareEisensteinSourceCoefficient_half_amplitude, norm_mul]
    have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [hhalf]
    change (1 / 2 : ℝ) * ‖Q j‖ ≤ ‖Q j‖
    nlinarith only [norm_nonneg (Q j)]
  have hcross :
      ‖∑ j : Gamma0EisensteinCuspClasses N,
        gamma0BareEisensteinSourceCoefficient N j r Y hY m hm t *
          star (gamma0BareEisensteinSourceCoefficient N j s Y hY n hn t)‖ ≤
        ((∑ j, ‖P j‖ ^ 2) + (∑ j, ‖Q j‖ ^ 2)) / 2 := by
    calc
      _ ≤ ∑ j : Gamma0EisensteinCuspClasses N,
          ‖gamma0BareEisensteinSourceCoefficient N j r Y hY m hm t *
            star (gamma0BareEisensteinSourceCoefficient N j s Y hY n hn t)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ j : Gamma0EisensteinCuspClasses N, (‖P j‖ ^ 2 + ‖Q j‖ ^ 2) / 2 := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul, norm_star]
        have hmul := mul_le_mul (ha j) (hb j) (norm_nonneg _) (norm_nonneg _)
        nlinarith only [hmul, sq_nonneg (‖P j‖ - ‖Q j‖)]
      _ = _ := by rw [← Finset.sum_div, Finset.sum_add_distrib]
  have hD : 0 ≤ gamma0ContinuousPrincipalDensity N r Y hY m hm t +
      gamma0ContinuousPrincipalDensity N s Y hY n hn t :=
    add_nonneg
      (div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) hW.le)
      (div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) hW.le)
  rw [gamma0BareContinuousRhoIntegrand, spectralJClippedEnergyTest_continuous_symbol,
    norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg (by positivity : 0 ≤ 2 * Real.pi),
    spectralJForwardSpectralWeight_norm_real]
  change ((Real.pi / W) * ‖spectralJForwardTransform f (t : ℂ)‖ / (2 * Real.pi)) *
    ‖_‖ ≤ (C / 4) * (_ + _)
  calc
    _ ≤ ((Real.pi / W) * ‖spectralJForwardTransform f (t : ℂ)‖ / (2 * Real.pi)) *
        (((∑ j, ‖P j‖ ^ 2) + (∑ j, ‖Q j‖ ^ 2)) / 2) :=
      mul_le_mul_of_nonneg_left hcross (by positivity)
    _ = (‖spectralJForwardTransform f (t : ℂ)‖ / 4) *
        (gamma0ContinuousPrincipalDensity N r Y hY m hm t +
          gamma0ContinuousPrincipalDensity N s Y hY n hn t) := by
      dsimp only [gamma0ContinuousPrincipalDensity, gamma0ContinuousFourierMass, P, Q, W]
      field_simp [Real.pi_ne_zero, (Real.cosh_pos (Real.pi * t)).ne'] <;> ring
    _ ≤ ((C / (1 + |t|) ^ 4) / 4) *
        (gamma0ContinuousPrincipalDensity N r Y hY m hm t +
          gamma0ContinuousPrincipalDensity N s Y hY n hn t) :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (hbound t) (by norm_num)) hD
    _ = _ := by ring

end
end ArtinMatthews
