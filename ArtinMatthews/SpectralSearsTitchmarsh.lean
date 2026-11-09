module

public import ArtinMatthews.SpectralJGaussianTailContinuity
public import ArtinMatthews.SpectralGaussianPlainUniqueness
public import ArtinMatthews.SpectralJGaussianDecay
public import ArtinMatthews.SpectralJOddSynthesisCalibration
public import ArtinMatthews.SpectralJWeightedGaussian
public import ArtinMatthews.SpectralJGaussianBridge


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Set
open OAI.CubicEisenstein
open scoped ContDiff
noncomputable section

def spectralJGaussianRemainder (f : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ((1 / Real.sqrt (8 * Real.pi) : ℝ) : ℂ) *
    spectralJGaussianTail (spectralJGaussianTransform f) Y

private theorem gaussian_exp_real (p x : ℝ) :
    Complex.exp (-(p : ℂ) * (x : ℂ) ^ 2) = (Real.exp (-(p * x ^ 2)) : ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1 <;> push_cast <;> ring

private theorem gaussian_sqrt_factor (p : ℝ) (hp : 0 < p) :
    Real.sqrt (Real.pi / p) * Real.sqrt (1 / (8 * p)) /
      Real.sqrt (8 * Real.pi) = 1 / (8 * p) := by
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  rw [div_pow, mul_pow, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  field_simp [hp.ne', Real.pi_ne_zero]
  <;> ring

theorem spectralJGaussianRemainder_continuousOn (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioi (0 : ℝ)) :
    ContinuousOn (spectralJGaussianRemainder f) (Ioi (0 : ℝ)) := by
  have hfi : IntegrableOn f (Ioi (0 : ℝ)) :=
    (hf.continuous.integrable_of_hasCompactSupport hc).integrableOn
  have hF := (spectralJGaussianTransform_continuous f hf.continuous hfi).measurable
  exact continuousOn_const.mul (spectralJGaussianTail_continuousOn _ hF
    (spectralJGaussianTransform_integrableOn_tail f hf hc hs))

theorem spectralJ_reconstruction_gaussian (f H : ℝ → ℂ)
    (hf : Continuous f) (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ioi (0 : ℝ))
    (hH : AEMeasurable H spectralKLSpectralMeasure)
    (hW : Integrable (fun r : ℝ => ‖H r‖ *
      (1 + (Real.sqrt (Real.cosh Real.pi) / Real.pi) / r)) spectralKLSpectralMeasure)
    (hInv : ∀ Y : ℝ, 0 < Y →
      (∫ r : ℝ, schlafliBesselK ((r : ℂ) * Complex.I) Y * H r
        ∂spectralKLSpectralMeasure) = spectralJGaussianRemainder f Y)
    (p : ℝ) (hp : 1 / 4 < p) :
    (∫ x in Ioi (0 : ℝ), Complex.exp (-(p : ℂ) * (x : ℂ) ^ 2) * f x) =
      (∫ x in Ioi (0 : ℝ), Complex.exp (-(p : ℂ) * (x : ℂ) ^ 2) *
        spectralJWeightedSynthesis H x) +
      ∫ x in Ioi (0 : ℝ), Complex.exp (-(p : ℂ) * (x : ℂ) ^ 2) *
        spectralJOddSynthesis f x := by
  have hp0 : 0 < p := by linarith
  let Y : ℝ := 1 / (8 * p)
  have hY : 0 < Y := by dsimp [Y]; positivity
  let I₀ : ℂ := ∫ u in (0 : ℝ)..1,
    (Real.exp (-u / (4 * p)) : ℂ) * spectralJGaussianTransform f (2 * u)
  let T : ℂ := ∫ w in Ioi (2 : ℝ),
    (Real.exp (-(Y * w)) : ℂ) * spectralJGaussianTransform f w
  let I : ℂ := ∫ x in Ioi (0 : ℝ),
    Complex.exp (-(p : ℂ) * (x : ℂ) ^ 2) * f x
  have hfi : IntegrableOn f (Ioi (0 : ℝ)) :=
    (hf.integrable_of_hasCompactSupport hc).integrableOn
  have hsplit : (2 : ℂ) * I₀ + T = (8 * p : ℝ) * I := by
    have h := (spectralJGaussianTransform_laplace_split f hf hfi Y hY).trans
      (spectralJGaussianTransform_laplace f hf hfi Y hY).symm
    have hscale := spectralJGaussianTransform_gaussian f hf hfi p hp0
    have hu (u : ℝ) : -(2 * Y * u) = -u / (4 * p) := by
      dsimp [Y]
      field_simp
      <;> ring
    have hx (x : ℝ) : f x * (Real.exp (-(p * x ^ 2)) : ℂ) =
        Complex.exp (-(p : ℂ) * (x : ℂ) ^ 2) * f x := by
      rw [gaussian_exp_real]
      ring
    simpa only [Y, hu, hx, I₀, T, I] using h.trans hscale
  have hodd : (∫ x in Ioi (0 : ℝ),
      Complex.exp (-(p : ℂ) * (x : ℂ) ^ 2) * spectralJOddSynthesis f x) =
      ((1 / (4 * p) : ℝ) : ℂ) * I₀ := by
    simpa only [gaussian_exp_real, I₀] using
      spectralJOddSynthesis_gaussian_calibrated f hf hc hs p hp
  have hcontinuous : (∫ x in Ioi (0 : ℝ),
      Complex.exp (-(p : ℂ) * (x : ℂ) ^ 2) * spectralJWeightedSynthesis H x) =
      (Y : ℂ) * T := by
    rw [spectralJWeightedSynthesis_gaussian H hH hW hp, hInv Y hY]
    unfold spectralJGaussianRemainder spectralJGaussianTail
    rw [if_pos hY]
    change ((Real.sqrt (Real.pi / p) : ℂ) * Complex.exp (-(Y : ℂ))) *
      (((1 / Real.sqrt (8 * Real.pi) : ℝ) : ℂ) *
        (((Real.sqrt Y * Real.exp Y : ℝ) : ℂ) * T)) = (Y : ℂ) * T
    rw [Complex.ofReal_mul, Complex.ofReal_exp]
    have hfactor : (Real.sqrt (Real.pi / p) : ℂ) *
        ((1 / Real.sqrt (8 * Real.pi) : ℝ) : ℂ) * (Real.sqrt Y : ℂ) = (Y : ℂ) := by
      have hreal := gaussian_sqrt_factor p hp0
      change (Real.sqrt (Real.pi / p) : ℂ) *
        ((1 / Real.sqrt (8 * Real.pi) : ℝ) : ℂ) *
          (Real.sqrt (1 / (8 * p)) : ℂ) = ((1 / (8 * p) : ℝ) : ℂ)
      have hreal' : Real.sqrt (Real.pi / p) * (1 / Real.sqrt (8 * Real.pi)) *
          Real.sqrt (1 / (8 * p)) = 1 / (8 * p) := by
        simpa only [div_eq_mul_inv, one_div, one_mul, mul_assoc, mul_left_comm, mul_comm] using hreal
      exact_mod_cast hreal'
    have hexp : Complex.exp (-(Y : ℂ)) * Complex.exp (Y : ℂ) = 1 := by
      rw [← Complex.exp_add]
      simp
    calc
      _ = ((Real.sqrt (Real.pi / p) : ℂ) *
          ((1 / Real.sqrt (8 * Real.pi) : ℝ) : ℂ) * (Real.sqrt Y : ℂ)) *
          (Complex.exp (-(Y : ℂ)) * Complex.exp (Y : ℂ)) * T := by ring
      _ = _ := by rw [hfactor, hexp, mul_one]
  rw [hcontinuous, hodd]
  change I = (Y : ℂ) * T + ((1 / (4 * p) : ℝ) : ℂ) * I₀
  have hpC : (p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp0.ne'
  apply mul_left_cancel₀ (show (8 : ℂ) * (p : ℂ) ≠ 0 from mul_ne_zero (by norm_num) hpC)
  calc
    _ = T + 2 * I₀ := by push_cast at hsplit; linear_combination -hsplit
    _ = _ := by dsimp [Y]; push_cast; field_simp [hpC] <;> ring

theorem spectralJ_reconstruction_of_completed_analysis (f H : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioi (0 : ℝ)) (hHs : ContDiff ℝ ∞ H)
    (hHr : SpectralKLDirectRapid H)
    (hW : Integrable (fun r : ℝ => ‖H r‖ *
      (1 + (Real.sqrt (Real.cosh Real.pi) / Real.pi) / r)) spectralKLSpectralMeasure)
    (hAnalysis : ∃ hG : MemLp (spectralJGaussianRemainder f) 2 spectralKLPhysicalMeasure,
      spectralKLAnalysis (hG.toLp (spectralJGaussianRemainder f)) =ᵐ[spectralKLSpectralMeasure] H) :
    EqOn f (fun x => spectralJWeightedSynthesis H x + spectralJOddSynthesis f x)
      (Ioi (0 : ℝ)) := by
  obtain ⟨hG, hA⟩ := hAnalysis
  have hpoint := spectralKLContinuousPointwiseInverse _ H hG
    (spectralJGaussianRemainder_continuousOn f hf hc hs) hHs.contDiffOn hHs.continuous hHr hA
  have hInv (Y : ℝ) (hY : 0 < Y) :
      (∫ r : ℝ, schlafliBesselK ((r : ℂ) * Complex.I) Y * H r
        ∂spectralKLSpectralMeasure) = spectralJGaussianRemainder f Y := by
    have he : (∫ r : ℝ, schlafliBesselK ((r : ℂ) * Complex.I) Y * H r
        ∂spectralKLSpectralMeasure) = spectralKLWeightedSynthesis H Y := by
      rw [spectralKLSpectralMeasure, spectralKLPositiveWeightMeasure_complex_integral _ _
        spectralKLPlancherelWeight_continuous.measurable
        (fun r hr => (spectralKLPlancherelWeight_pos hr).le), spectralKLWeightedSynthesis]
      apply integral_congr_ae
      filter_upwards with r
      ring
    rw [he]
    simpa only [spectralKLDirectSynthesis, if_pos hY] using hpoint hY
  apply spectral_eqOn_Ioi_of_plain_gaussian_eq f
    (fun x => spectralJWeightedSynthesis H x + spectralJOddSynthesis f x)
    hf.continuous.continuousOn
    ((spectralJWeightedSynthesis_continuousOn H hHs.continuous.measurable.aemeasurable hW).add
      (spectralJOddSynthesis_continuous f hf.continuous hc hs).continuousOn) (1 / 4)
  · intro p hp
    have he : Continuous (fun x : ℝ => Complex.exp (-(p : ℂ) * (x : ℂ) ^ 2)) := by fun_prop
    exact (he.mul hf.continuous).integrable_of_hasCompactSupport hc.mul_left |>.integrableOn
  · intro p hp
    have h₁ := spectralJWeightedSynthesis_gaussian_integrable H hHs.continuous.measurable.aemeasurable hW hp
    have h₂ := spectralJOddSynthesis_gaussian_integrable f hf.continuous hc hs p hp
    have hadd := h₁.add h₂
    change IntegrableOn (fun x : ℝ =>
      Complex.exp (-(p : ℂ) * (x : ℂ) ^ 2) * spectralJWeightedSynthesis H x +
        (Real.exp (-(p * x ^ 2)) : ℂ) * spectralJOddSynthesis f x)
      (Ioi (0 : ℝ)) at hadd
    simpa only [gaussian_exp_real, mul_add] using hadd
  · intro p hp
    have h₁ := spectralJWeightedSynthesis_gaussian_integrable H
      hHs.continuous.measurable.aemeasurable hW hp
    have h₂ : IntegrableOn (fun x : ℝ =>
        Complex.exp (-(p : ℂ) * (x : ℂ) ^ 2) * spectralJOddSynthesis f x)
        (Ioi (0 : ℝ)) := by
      simpa only [gaussian_exp_real] using
        spectralJOddSynthesis_gaussian_integrable f hf.continuous hc hs p hp
    have hsum : (∫ x in Ioi (0 : ℝ), Complex.exp (-(p : ℂ) * (x : ℂ) ^ 2) *
        (spectralJWeightedSynthesis H x + spectralJOddSynthesis f x)) =
        (∫ x in Ioi (0 : ℝ), Complex.exp (-(p : ℂ) * (x : ℂ) ^ 2) *
          spectralJWeightedSynthesis H x) +
        ∫ x in Ioi (0 : ℝ), Complex.exp (-(p : ℂ) * (x : ℂ) ^ 2) *
          spectralJOddSynthesis f x := by
      simp only [mul_add]
      exact integral_add h₁ h₂
    exact (spectralJ_reconstruction_gaussian f H hf.continuous hc hs
      hHs.continuous.measurable.aemeasurable hW hInv p hp).trans hsum.symm

end
end ArtinMatthews
