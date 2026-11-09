module

public import ArtinMatthews.SpectralEisensteinTestMultiplier


set_option backward.privateInPublic true
@[expose] public section

/-! Forward weighted pairings use the original compact Eisenstein tests.
Parseval also holds for arbitrary vectors in the full channel L² space. -/
noncomputable section
open Set Filter MeasureTheory
open scoped InnerProductSpace
namespace ArtinMatthews

theorem gamma0EisensteinChannelPair_seed_ae (N : ℕ) [NeZero N] (ψ ξ : h2SmoothCompactSeeds) :
    gamma0EisensteinChannelPair N (gamma0EisensteinAnalysis N (gamma0SmoothSeedMass N ψ))
      (gamma0EisensteinAnalysis N (gamma0SmoothSeedMass N ξ))=ᵐ[gamma0EisensteinSpectralMeasure]
      fun t => ∑ i : Gamma0EisensteinCuspClasses N,gamma0StoneEisensteinAmplitude N ψ i t*
        (starRingEnd ℂ) (gamma0StoneEisensteinAmplitude N ξ i t) := by
  rw [gamma0EisensteinAnalysis_seed,gamma0EisensteinAnalysis_seed]
  have hψ : ∀ᵐ t ∂gamma0EisensteinSpectralMeasure,∀ i : Gamma0EisensteinCuspClasses N,
      gamma0EisensteinCoefficientLp N i ψ t=(starRingEnd ℂ) (gamma0StoneEisensteinAmplitude N ψ i t) :=
    ae_all_iff.mpr (fun i => gamma0EisensteinCoefficientLp_ae N i ψ)
  have hξ : ∀ᵐ t ∂gamma0EisensteinSpectralMeasure,∀ i : Gamma0EisensteinCuspClasses N,
      gamma0EisensteinCoefficientLp N i ξ t=(starRingEnd ℂ) (gamma0StoneEisensteinAmplitude N ξ i t) :=
    ae_all_iff.mpr (fun i => gamma0EisensteinCoefficientLp_ae N i ξ)
  filter_upwards [hψ,hξ] with t htψ htξ
  unfold gamma0EisensteinChannelPair
  apply Finset.sum_congr rfl
  intro i _
  rw [gamma0EisensteinSeedAnalysis_apply,gamma0EisensteinSeedAnalysis_apply,htψ i,htξ i,RCLike.inner_apply,
    show (starRingEnd ℂ) ((starRingEnd ℂ) (gamma0StoneEisensteinAmplitude N ψ i t))=
      gamma0StoneEisensteinAmplitude N ψ i t from star_star _]
  ring

theorem gamma0ContinuousTestOperator_compact_integrable (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (ψ ξ : h2SmoothCompactSeeds) :
    IntegrableOn (fun t => spectralContinuousTestSymbol h t*gamma0StoneEisensteinPairIntegrand N ψ ξ t) (Ioi 0) :=
  (gamma0StoneEisensteinPairIntegrand_integrableOn N ψ ξ).bdd_mul
    (spectralContinuousTestSymbol h).continuous.measurable.aestronglyMeasurable
    (ae_of_all _ (fun t => (spectralContinuousTestSymbol h).norm_coe_le_norm t))

theorem gamma0ContinuousTestOperator_compact_pair (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (ψ ξ : h2SmoothCompactSeeds) :
    inner ℂ (gamma0SmoothSeedMass N ψ) (gamma0ContinuousTestOperator N h (gamma0SmoothSeedMass N ξ))=
      ∫ t in Ioi 0,spectralContinuousTestSymbol h t*gamma0StoneEisensteinPairIntegrand N ψ ξ t := by
  rw [gamma0ContinuousTestOperator_pair]
  calc
    _ = ∫ t,spectralContinuousTestSymbol h t*(∑ i : Gamma0EisensteinCuspClasses N,
      gamma0StoneEisensteinAmplitude N ψ i t*(starRingEnd ℂ) (gamma0StoneEisensteinAmplitude N ξ i t))
        ∂gamma0EisensteinSpectralMeasure := by
      apply integral_congr_ae
      filter_upwards [gamma0EisensteinChannelPair_seed_ae N ψ ξ] with t ht
      rw [ht]
    _ = _ := by
      have hp : 0≤(2*Real.pi)⁻¹ := by positivity
      rw [gamma0EisensteinSpectralMeasure,integral_smul_measure,ENNReal.toReal_ofReal hp,
        Complex.real_smul,← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ (fun t => by
        change (((2*Real.pi)⁻¹:ℝ):ℂ)*(spectralContinuousTestSymbol h t*(∑ i,
          gamma0StoneEisensteinAmplitude N ψ i t*(starRingEnd ℂ) (gamma0StoneEisensteinAmplitude N ξ i t)))=
          spectralContinuousTestSymbol h t*gamma0StoneEisensteinPairIntegrand N ψ ξ t
        rw [gamma0StoneEisensteinPairIntegrand,Complex.ofReal_inv]
        ring)

theorem gamma0EisensteinSynthesis_parseval_integral (N : ℕ) [NeZero N]
    (f : Gamma0EisensteinSpectralSpace N) :
    ‖(gamma0EisensteinAnalysis N).adjoint f‖^2=
      ∫ t,(∑ i : Gamma0EisensteinCuspClasses N,‖f i t‖^2) ∂gamma0EisensteinSpectralMeasure := by
  rw [gamma0EisensteinSynthesis_norm,PiLp.norm_sq_eq_of_L2]
  have he (i : Gamma0EisensteinCuspClasses N) :
      ‖f i‖^2=∫ t,‖f i t‖^2 ∂gamma0EisensteinSpectralMeasure := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  simp_rw [he]
  exact (integral_finsetSum Finset.univ (fun i _ =>
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (f i))).mp (Lp.memLp (f i)))).symm

end ArtinMatthews
