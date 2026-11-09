module

public import ArtinMatthews.SpectralJWeightedSynthesis


set_option backward.privateInPublic true
@[expose] public section

/-! Gaussian integration of the weighted continuous J synthesis. The
spectral coefficient can be merely a.e. measurable with finite weighted
absolute integral. The actual Gaussian multiplier and the actual KL
measure occur in the resulting Fubini identity. -/
namespace ArtinMatthews
open Set MeasureTheory Filter
open OAI.CubicEisenstein

noncomputable section

private theorem spectralJWeightedGaussian_aestronglyMeasurable
    (H : ℝ → ℂ) (hH : AEMeasurable H spectralKLSpectralMeasure) (p : ℝ) :
    AEStronglyMeasurable
      (spectralWeylGaussianSpectralIntegrand spectralWeylJMultiplier p H (fun _ => 1))
      ((volume.restrict (Ioi (0 : ℝ))).prod spectralKLSpectralMeasure) := by
  have h1 : Measurable (fun _ : ℝ => (1 : ℂ)) := measurable_const
  have hI := spectralWeylGaussianSpectralIntegrand_measurable spectralWeylJMultiplier p
    (fun _ => 1) (fun _ => 1) spectralWeylJMultiplier_measurable h1 h1
  have hs : AEMeasurable (fun q : ℝ × ℝ => H q.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod spectralKLSpectralMeasure) :=
    hH.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have he :
      spectralWeylGaussianSpectralIntegrand spectralWeylJMultiplier p H (fun _ => 1) =
      fun q => spectralWeylGaussianSpectralIntegrand spectralWeylJMultiplier p
        (fun _ => 1) (fun _ => 1) q * H q.2 := by
    funext q
    simp only [spectralWeylGaussianSpectralIntegrand, star_one, mul_one]
  rw [he]
  exact (hI.aemeasurable.mul hs).aestronglyMeasurable

theorem spectralJWeightedGaussian_pair_integrable (H : ℝ → ℂ)
    (hH : AEMeasurable H spectralKLSpectralMeasure)
    (hW : Integrable (fun r : ℝ =>
      ‖H r‖ * (1 + (Real.sqrt (Real.cosh Real.pi) / Real.pi) / r)) spectralKLSpectralMeasure)
    {p : ℝ} (hp : 1/4 < p) :
    Integrable (spectralWeylGaussianSpectralIntegrand spectralWeylJMultiplier p H (fun _ => 1))
      ((volume.restrict (Ioi (0 : ℝ))).prod spectralKLSpectralMeasure) := by
  have hX : Integrable (fun x : ℝ => 4*Real.pi*Real.exp (-(p-1/4)*x^2))
      (volume.restrict (Ioi (0 : ℝ))) :=
    ((integrable_exp_neg_mul_sq (sub_pos.mpr hp)).const_mul (4*Real.pi)).restrict
  apply (hX.mul_prod hW).mono' (spectralJWeightedGaussian_aestronglyMeasurable H hH p)
  have hpos : ∀ᵐ q ∂((volume.restrict (Ioi (0 : ℝ))).prod spectralKLSpectralMeasure),
      0 < q.1 ∧ 0 < q.2 := by
    apply (Measure.ae_prod_iff_ae_ae ((measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_const measurable_snd))).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    filter_upwards [spectralKLPositiveWeightMeasure_ae_pos spectralKLPlancherelWeight] with r hr
    exact ⟨hx,hr⟩
  filter_upwards [hpos] with q hq
  have hb := spectralWeylGaussianSpectralIntegrand_bound spectralWeylJMultiplier p
    (Real.sqrt (Real.cosh Real.pi)/Real.pi) H (fun _ => 1)
    (spectralWeylJMultiplier_order_bound hq.2 hq.1)
  simpa only [norm_one, mul_one] using hb

private theorem spectralJWeightedSynthesis_gaussian_integrand_eq (H : ℝ → ℂ) (p x : ℝ) :
    Complex.exp (-(p : ℂ)*(x : ℂ)^2) * spectralJWeightedSynthesis H x =
      (1/2 : ℂ) * (Complex.exp (-(p : ℂ)*(x : ℂ)^2) * (x : ℂ) *
        spectralWeylSpectralBilinear spectralWeylJMultiplier H (fun _ => 1) x) := by
  simp only [spectralJWeightedSynthesis, spectralWeylSpectralBilinear, star_one, mul_one]
  ring

theorem spectralJWeightedSynthesis_gaussian_integrable (H : ℝ → ℂ)
    (hH : AEMeasurable H spectralKLSpectralMeasure)
    (hW : Integrable (fun r : ℝ =>
      ‖H r‖ * (1 + (Real.sqrt (Real.cosh Real.pi) / Real.pi) / r)) spectralKLSpectralMeasure)
    {p : ℝ} (hp : 1/4 < p) :
    IntegrableOn (fun x : ℝ =>
      Complex.exp (-(p : ℂ)*(x : ℂ)^2) * spectralJWeightedSynthesis H x) (Ioi 0) := by
  have hi := spectralWeylSpectralBilinear_gaussian_integrable spectralWeylJMultiplier p H
    (fun _ => 1) (spectralJWeightedGaussian_pair_integrable H hH hW hp)
  apply (hi.const_mul (1/2 : ℂ)).congr
  filter_upwards with x
  exact (spectralJWeightedSynthesis_gaussian_integrand_eq H p x).symm

theorem spectralJWeightedSynthesis_gaussian (H : ℝ → ℂ)
    (hH : AEMeasurable H spectralKLSpectralMeasure)
    (hW : Integrable (fun r : ℝ =>
      ‖H r‖ * (1 + (Real.sqrt (Real.cosh Real.pi) / Real.pi) / r)) spectralKLSpectralMeasure)
    {p : ℝ} (hp : 1/4 < p) :
    (∫ x in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(x : ℂ)^2) * spectralJWeightedSynthesis H x) =
      ((Real.sqrt (Real.pi/p) : ℂ) * Complex.exp (-((1/(8*p) : ℝ) : ℂ))) *
        (∫ r : ℝ, schlafliBesselK ((r : ℂ)*Complex.I) (1/(8*p)) * H r ∂spectralKLSpectralMeasure) := by
  have hp0 : 0 < p := by linarith
  simp_rw [spectralJWeightedSynthesis_gaussian_integrand_eq]
  rw [integral_const_mul]
  simp only [spectralWeylSpectralBilinear]
  rw [spectralWeyl_gaussian_spectral_swap spectralWeylJMultiplier p H (fun _ => 1)
    (spectralJWeightedGaussian_pair_integrable H hH hW hp)]
  conv_lhs => rw [← integral_const_mul]
  conv_rhs => rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [spectralKLPositiveWeightMeasure_ae_pos spectralKLPlancherelWeight] with r hr
  rw [spectralWeylJMultiplier_gaussian_value hr hp0]
  simp only [star_one, mul_one]
  ring

end
end ArtinMatthews
