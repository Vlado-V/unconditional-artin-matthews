module

public import ArtinMatthews.SpectralCriticalSquareIntegrability
public import ArtinMatthews.SpectralStoneEisensteinSesquilinear


set_option backward.privateInPublic true
@[expose] public section

/-! The actual compact Eisenstein tests have no critical poles. Their
canonical values are analytic in the spectral parameter and preserve
the proved positive-frequency pairings. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped MatrixGroups
namespace ArtinMatthews

theorem gamma0StoneEisensteinAmplitude_sq_integrableOn (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (i : Gamma0EisensteinCuspClasses N) :
    IntegrableOn (fun t => ‖gamma0StoneEisensteinAmplitude N ψ i t‖^2) (Ioi 0) := by
  have hd := (gamma0StoneFrequencyDensity_integrableOn N ψ (gamma0CompactResolventCutoff N ψ)).const_mul (2*Real.pi)
  apply hd.mono' ((gamma0StoneEisensteinAmplitude_measurable N ψ i).norm.pow_const 2).aestronglyMeasurable
  exact ae_of_all _ fun t => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ ∑ j,‖gamma0StoneEisensteinAmplitude N ψ j t‖^2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      _ = (2*Real.pi)*gamma0StoneFrequencyDensity N ψ t := by
        unfold gamma0StoneFrequencyDensity gamma0StoneEisensteinAmplitude
        field_simp [Real.pi_ne_zero]

theorem gamma0CuspEisensteinMeromorphicTest_order_critical (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (i : Gamma0EisensteinCuspClasses N) (t : ℝ) (ht : 0≤t) :
    0 ≤ meromorphicOrderAt
      (gamma0CuspEisensteinMeromorphicTest N (gamma0EisensteinCuspClassRepresentative N i) ψ)
      (eisensteinCriticalPoint t) :=
  spectralMeromorphic_order_critical_nonneg_of_sq_integrable _ t ht
    (gamma0CuspEisensteinMeromorphicTest_meromorphic N (gamma0EisensteinCuspClassRepresentative N i) ψ _)
    (gamma0StoneEisensteinAmplitude_sq_integrableOn N ψ i)

def gamma0CuspEisensteinCanonicalTest (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (ψ : h2SmoothCompactSeeds) (s : ℂ) : ℂ :=
  toMeromorphicNFOn (gamma0CuspEisensteinMeromorphicTest N a ψ) univ s

theorem gamma0CuspEisensteinCanonicalTest_analyticAt_critical (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (i : Gamma0EisensteinCuspClasses N) (t : ℝ) (ht : 0≤t) :
    AnalyticAt ℂ (gamma0CuspEisensteinCanonicalTest N (gamma0EisensteinCuspClassRepresentative N i) ψ)
      (eisensteinCriticalPoint t) := by
  let f := gamma0CuspEisensteinMeromorphicTest N (gamma0EisensteinCuspClassRepresentative N i) ψ
  have h := meromorphicNFOn_toMeromorphicNFOn f univ (mem_univ (eisensteinCriticalPoint t))
  apply h.meromorphicOrderAt_nonneg_iff_analyticAt.mp
  rw [meromorphicOrderAt_toMeromorphicNFOn
    (fun s _ => gamma0CuspEisensteinMeromorphicTest_meromorphic N
      (gamma0EisensteinCuspClassRepresentative N i) ψ s) (mem_univ _)]
  exact gamma0CuspEisensteinMeromorphicTest_order_critical N ψ i t ht

theorem gamma0CuspEisensteinCanonicalTest_eq_of_analytic (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (ψ : h2SmoothCompactSeeds) (s : ℂ)
    (hs : AnalyticAt ℂ (gamma0CuspEisensteinMeromorphicTest N a ψ) s) :
    gamma0CuspEisensteinCanonicalTest N a ψ s=gamma0CuspEisensteinMeromorphicTest N a ψ s := by
  unfold gamma0CuspEisensteinCanonicalTest
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt
    (fun w _ => gamma0CuspEisensteinMeromorphicTest_meromorphic N a ψ w) (mem_univ s),
    toMeromorphicNFAt_eq_self.mpr hs.meromorphicNFAt]

theorem gamma0CuspEisensteinCanonicalTest_critical_ae (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (ψ : h2SmoothCompactSeeds) :
    (fun t : ℝ => gamma0CuspEisensteinCanonicalTest N a ψ (eisensteinCriticalPoint t))
      =ᵐ[volume] fun t => gamma0CuspEisensteinMeromorphicTest N a ψ (eisensteinCriticalPoint t) := by
  let f := gamma0CuspEisensteinMeromorphicTest N a ψ
  have hc : (eisensteinCriticalPoint ⁻¹' {s | AnalyticAt ℂ f s}ᶜ).Countable :=
    (gamma0CuspEisensteinMeromorphicTest_meromorphic N a ψ).countable_compl_analyticAt.preimage
      eisensteinCriticalPoint_injective
  have hae : ∀ᵐ t ∂(volume:Measure ℝ),AnalyticAt ℂ f (eisensteinCriticalPoint t) :=
    ae_iff.mpr (hc.measure_zero volume)
  filter_upwards [hae] with t ht
  exact gamma0CuspEisensteinCanonicalTest_eq_of_analytic N a ψ (eisensteinCriticalPoint t) ht

theorem gamma0StoneEisensteinPair_eq_canonical_integral (N : ℕ) [NeZero N]
    (ψ ξ : h2SmoothCompactSeeds) :
    gamma0StoneEisensteinPair N ψ ξ=
      ∫ t in Ioi 0,
        (∑ i,gamma0CuspEisensteinCanonicalTest N (gamma0EisensteinCuspClassRepresentative N i) ψ
            (eisensteinCriticalPoint t)*
          (starRingEnd ℂ) (gamma0CuspEisensteinCanonicalTest N
            (gamma0EisensteinCuspClassRepresentative N i) ξ (eisensteinCriticalPoint t)))/
          ((2*Real.pi:ℝ):ℂ) := by
  have hψ : ∀ᵐ t ∂(volume:Measure ℝ),∀ i : Gamma0EisensteinCuspClasses N,
      gamma0CuspEisensteinCanonicalTest N (gamma0EisensteinCuspClassRepresentative N i) ψ
        (eisensteinCriticalPoint t)=gamma0StoneEisensteinAmplitude N ψ i t :=
    ae_all_iff.mpr (fun i => gamma0CuspEisensteinCanonicalTest_critical_ae N _ ψ)
  have hξ : ∀ᵐ t ∂(volume:Measure ℝ),∀ i : Gamma0EisensteinCuspClasses N,
      gamma0CuspEisensteinCanonicalTest N (gamma0EisensteinCuspClassRepresentative N i) ξ
        (eisensteinCriticalPoint t)=gamma0StoneEisensteinAmplitude N ξ i t :=
    ae_all_iff.mpr (fun i => gamma0CuspEisensteinCanonicalTest_critical_ae N _ ξ)
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hψ,ae_restrict_of_ae hξ] with t htψ htξ
  simp only [htψ,htξ,gamma0StoneEisensteinPairIntegrand]

end ArtinMatthews
