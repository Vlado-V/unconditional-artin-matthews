module

public import ArtinMatthews.SpectralJGaussianFubini
public import ArtinMatthews.SpectralBesselLegendreTransform
public import ArtinMatthews.SpectralJOddCoefficients


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Set
noncomputable section

private def legendreTransformIntegrand (f : ℝ → ℂ) (n : ℕ) (z : ℝ × ℝ) : ℂ :=
  (spectralLegendreValue n z.2 : ℂ) * (f z.1 * spectralJGaussianKernel z.1 (2 * z.2))

private theorem legendreTransformIntegrand_continuous (f : ℝ → ℂ)
    (hf : Continuous f) (n : ℕ) : Continuous (legendreTransformIntegrand f n) := by
  have hL : Continuous (fun z : ℝ × ℝ => (spectralLegendreValue n z.2 : ℂ)) :=
    Complex.continuous_ofReal.comp ((spectralLegendreValue_continuous n).comp continuous_snd)
  have hpair : Continuous (fun z : ℝ × ℝ => (z.1, (2 : ℝ) * z.2)) :=
    continuous_fst.prodMk (continuous_const.mul continuous_snd)
  have hK : Continuous (fun z : ℝ × ℝ => spectralJGaussianKernel z.1 (2 * z.2)) := by
    simpa only [Function.comp_def] using spectralJGaussianKernel_continuous.comp hpair
  exact hL.mul ((hf.comp continuous_fst).mul hK)

private theorem legendreTransformIntegrand_integrable (f : ℝ → ℂ)
    (hf : Continuous f) (hfi : IntegrableOn f (Ioi (0 : ℝ))) (n : ℕ) :
    Integrable (legendreTransformIntegrand f n)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let ν : Measure ℝ := volume.restrict (Ioc 0 1)
  let : IsFiniteMeasure ν := ⟨by
    change volume.restrict (Ioc (0 : ℝ) 1) univ < ⊤
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top⟩
  obtain ⟨M, hM, hP⟩ := spectralLegendreValue_unit_bound n
  obtain ⟨C, hC, hK⟩ := spectralJGaussianKernel_bound
  have hdom : Integrable (fun z : ℝ × ℝ => ‖f z.1‖ * (M * C)) (μ.prod ν) :=
    hfi.norm.mul_prod (integrable_const (M * C))
  have ha : ∀ᵐ u ∂ν, u ∈ Ioc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioc
  have hs : Measure.QuasiMeasurePreserving (Prod.snd : ℝ × ℝ → ℝ) (μ.prod ν) ν :=
    Measure.quasiMeasurePreserving_snd
  apply hdom.mono' (legendreTransformIntegrand_continuous f hf n).aestronglyMeasurable
  filter_upwards [hs.ae ha] with z hz
  have hPz := hP z.2 ⟨hz.1.le, hz.2⟩
  simp only [legendreTransformIntegrand, norm_mul, Complex.norm_real]
  calc
    _ ≤ M * (‖f z.1‖ * C) :=
      mul_le_mul hPz (mul_le_mul_of_nonneg_left (hK _ _) (norm_nonneg _))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hM
    _ = _ := by ring

theorem spectralJGaussianTransform_legendre_coefficient (f : ℝ → ℂ)
    (hf : Continuous f) (hfi : IntegrableOn f (Ioi (0 : ℝ))) (n : ℕ) :
    (∫ u in (0 : ℝ)..1, (spectralLegendreValue n u : ℂ) *
      spectralJGaussianTransform f (2 * u)) =
      2 * spectralJDiscreteCoefficient f (2 * n + 1) := by
  have hpair := legendreTransformIntegrand_integrable f hf hfi n
  have hswap := integral_integral_swap
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (ν := volume.restrict (Ioc (0 : ℝ) 1))
    (f := fun x u : ℝ => legendreTransformIntegrand f n (x, u)) hpair
  calc
    _ = ∫ u in Ioc (0 : ℝ) 1, ∫ x in Ioi (0 : ℝ),
        legendreTransformIntegrand f n (x, u) := by
      rw [intervalIntegral.integral_of_le zero_le_one]
      apply integral_congr_ae
      filter_upwards with u
      rw [spectralJGaussianTransform, ← integral_const_mul]
      rfl
    _ = ∫ x in Ioi (0 : ℝ), ∫ u in Ioc (0 : ℝ) 1,
        legendreTransformIntegrand f n (x, u) := hswap.symm
    _ = ∫ x in Ioi (0 : ℝ), 2 * ((f x / (x : ℂ)) *
        Complex.besselJ ((2 * n + 1 : ℕ) : ℂ) (x : ℂ)) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hK (u : ℝ) : spectralJGaussianKernel x (2 * u) =
          Complex.besselJ 0 ((x : ℂ) * (Real.sqrt u : ℂ)) := by
        unfold spectralJGaussianKernel
        rw [spectral_besselJ_zero_sqrt_argument x u hx.le,
          show (x ^ 2 / 8) * (2 * u) = (x / 2) ^ 2 * u by ring]
      calc
        _ = f x * (∫ u in (0 : ℝ)..1, (spectralLegendreValue n u : ℂ) *
            Complex.besselJ 0 ((x : ℂ) * (Real.sqrt u : ℂ))) := by
          rw [intervalIntegral.integral_of_le zero_le_one, ← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with u
          simp only [legendreTransformIntegrand, hK]
          ring
        _ = _ := by rw [spectral_shiftedLegendre_besselJ_zero n x hx]; ring
    _ = _ := by rw [integral_const_mul]; rfl

end
end ArtinMatthews
