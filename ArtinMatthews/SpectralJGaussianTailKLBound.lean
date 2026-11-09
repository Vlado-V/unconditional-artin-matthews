module

public import ArtinMatthews.SpectralJGaussianTail
public import ArtinMatthews.SpectralJGaussianTailFubini


set_option backward.privateInPublic true
@[expose] public section

/-! Literal KL integration of the Gaussian tail, with a bound in the
one-step radial decay constant. -/

namespace ArtinMatthews

open MeasureTheory Set OAI.CubicEisenstein

noncomputable section

private theorem tailKernel_eq_laplace (t y w : ℝ) (hy : 0 < y) :
    spectralJTailKernel t y w =
      ((Real.sqrt y * Real.exp y / y : ℝ) : ℂ) *
        schlafliBesselK ((t : ℂ) * Complex.I) y * (Real.exp (-(y * w)) : ℂ) := by
  have hpow : Real.sqrt y / y = y ^ (-(1 / 2) : ℝ) := by
    calc
      _ = y ^ (1 / 2 : ℝ) / y ^ (1 : ℝ) := by rw [Real.sqrt_eq_rpow, Real.rpow_one]
      _ = y ^ ((1 / 2 : ℝ) - 1) := (Real.rpow_sub hy _ _).symm
      _ = _ := by norm_num
  have hr : Real.exp (-((w - 1) * y)) * y ^ (-(1 / 2) : ℝ) =
      (Real.sqrt y * Real.exp y / y) * Real.exp (-(y * w)) := by
    rw [← hpow, show -((w - 1) * y) = y + -(y * w) by ring, Real.exp_add]
    ring
  rw [spectralJTailKernel, hr, Complex.ofReal_mul]
  ring

theorem spectralJGaussianTail_KLKernel_eq_inner (F : ℝ → ℂ) (t : ℝ) {y : ℝ} (hy : 0 < y) :
    spectralJGaussianTail F y * schlafliBesselK ((t : ℂ) * Complex.I) y / (y : ℂ) =
      ∫ w in Ioi (2 : ℝ), spectralJTailKernel t y w * F w := by
  rw [spectralJGaussianTail, ite_eq_left hy]
  calc
    _ = (((Real.sqrt y * Real.exp y / y : ℝ) : ℂ) *
        schlafliBesselK ((t : ℂ) * Complex.I) y) *
        (∫ w in Ioi (2 : ℝ), (Real.exp (-(y * w)) : ℂ) * F w) := by
      push_cast
      ring
    _ = _ := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro w _
      dsimp only
      rw [tailKernel_eq_laplace t y w hy]
      ring

theorem spectralJGaussianTail_KLIntegral_integrable (F : ℝ → ℂ) (hF : Measurable F)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ w : ℝ, 2 < w → ‖F w‖ ≤ B / w) (t : ℝ) :
    IntegrableOn (fun y : ℝ =>
      spectralJGaussianTail F y * schlafliBesselK ((t : ℂ) * Complex.I) y / (y : ℂ)) (Ioi 0) := by
  apply (spectralJTailKernel_pair_integrable F hF B hB hbound t).integral_prod_left.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact (spectralJGaussianTail_KLKernel_eq_inner F t hy).symm

theorem spectralJGaussianTail_KLIntegral_eq (F : ℝ → ℂ) (hF : Measurable F)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ w : ℝ, 2 < w → ‖F w‖ ≤ B / w) (t : ℝ) :
    (∫ y in Ioi (0 : ℝ),
      spectralJGaussianTail F y * schlafliBesselK ((t : ℂ) * Complex.I) y / (y : ℂ)) =
      ∫ w in Ioi (2 : ℝ), F w * (∫ y in Ioi (0 : ℝ), spectralJTailKernel t y w) := by
  calc
    _ = ∫ y in Ioi (0 : ℝ), ∫ w in Ioi (2 : ℝ), spectralJTailKernel t y w * F w :=
      setIntegral_congr_fun measurableSet_Ioi (fun _ hy => spectralJGaussianTail_KLKernel_eq_inner F t hy)
    _ = ∫ w in Ioi (2 : ℝ), ∫ y in Ioi (0 : ℝ), spectralJTailKernel t y w * F w :=
      spectralJTailKernel_integral_swap F hF B hB hbound t
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro w _
      dsimp only
      rw [integral_mul_const, mul_comm]

theorem spectralJGaussianTail_KLIntegral_norm_le (F : ℝ → ℂ) (hF : Measurable F)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ w : ℝ, 2 < w → ‖F w‖ ≤ B / w) (t : ℝ) :
    ‖∫ y in Ioi (0 : ℝ),
      spectralJGaussianTail F y * schlafliBesselK ((t : ℂ) * Complex.I) y / (y : ℂ)‖ ≤
      4 * spectralJTailKZeroMellinMass * B := by
  obtain ⟨hp, hb⟩ := spectralJTailKernel_pair_integrable_and_bound F hF B hB hbound t
  have he : (∫ y in Ioi (0 : ℝ),
      spectralJGaussianTail F y * schlafliBesselK ((t : ℂ) * Complex.I) y / (y : ℂ)) =
      ∫ y in Ioi (0 : ℝ), ∫ w in Ioi (2 : ℝ), spectralJTailKernel t y w * F w :=
    setIntegral_congr_fun measurableSet_Ioi (fun _ hy => spectralJGaussianTail_KLKernel_eq_inner F t hy)
  rw [he]
  calc
    _ ≤ ∫ y in Ioi (0 : ℝ), ‖∫ w in Ioi (2 : ℝ), spectralJTailKernel t y w * F w‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y in Ioi (0 : ℝ), ∫ w in Ioi (2 : ℝ), ‖spectralJTailKernel t y w * F w‖ := by
      apply integral_mono_ae hp.integral_prod_left.norm hp.integral_norm_prod_left
      filter_upwards with y
      exact norm_integral_le_integral_norm _
    _ ≤ _ := hb

end
end ArtinMatthews
