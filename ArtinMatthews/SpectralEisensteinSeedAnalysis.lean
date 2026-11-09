module

public import ArtinMatthews.SpectralEisensteinCoefficientLp
public import ArtinMatthews.SpectralStoneNativePairing


set_option backward.privateInPublic true
@[expose] public section

/-! The literal finite-cusp Eisenstein analysis of a compact seed has the
exact continuum norm and is bounded by its actual ambient mass. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal MatrixGroups InnerProductSpace
namespace ArtinMatthews

abbrev Gamma0EisensteinSpectralSpace (N : ℕ) [NeZero N] :=
  PiLp 2 (fun _ : Gamma0EisensteinCuspClasses N => Lp ℂ 2 gamma0EisensteinSpectralMeasure)

def gamma0EisensteinSeedAnalysis (N : ℕ) [NeZero N] :
    h2SmoothCompactSeeds →ₗ[ℂ] Gamma0EisensteinSpectralSpace N :=
  (PiLp.continuousLinearEquiv 2 ℂ
    (fun _ : Gamma0EisensteinCuspClasses N => Lp ℂ 2 gamma0EisensteinSpectralMeasure)).symm.toLinearMap.comp
      (LinearMap.pi (gamma0EisensteinCoefficientLinear N))

theorem gamma0EisensteinSeedAnalysis_apply (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (i : Gamma0EisensteinCuspClasses N) :
    gamma0EisensteinSeedAnalysis N ψ i=gamma0EisensteinCoefficientLp N i ψ := rfl

theorem gamma0EisensteinSeedAnalysis_norm_sq (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) :
    ‖gamma0EisensteinSeedAnalysis N ψ‖^2=∫ t in Ioi 0,gamma0StoneFrequencyDensity N ψ t := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp_rw [gamma0EisensteinSeedAnalysis_apply,gamma0EisensteinCoefficientLp_norm_sq]
  rw [← Finset.mul_sum]
  have hs : (∑ i : Gamma0EisensteinCuspClasses N,∫ t in Ioi 0,
      ‖gamma0StoneEisensteinAmplitude N ψ i t‖^2)=
      ∫ t in Ioi 0,∑ i : Gamma0EisensteinCuspClasses N,‖gamma0StoneEisensteinAmplitude N ψ i t‖^2 :=
    (integral_finsetSum Finset.univ (fun i _ => gamma0StoneEisensteinAmplitude_sq_integrableOn N ψ i)).symm
  rw [hs]
  change (2*Real.pi)⁻¹*(∫ t in Ioi 0,∑ i : Gamma0EisensteinCuspClasses N,
      ‖gamma0StoneEisensteinAmplitude N ψ i t‖^2)=
    ∫ t in Ioi 0,(∑ i : Gamma0EisensteinCuspClasses N,‖gamma0StoneEisensteinAmplitude N ψ i t‖^2)/(2*Real.pi)
  rw [integral_div]
  ring

theorem gamma0EisensteinSeedAnalysis_norm_le (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) :
    ‖gamma0EisensteinSeedAnalysis N ψ‖≤‖gamma0SmoothSeedMass N ψ‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [gamma0EisensteinSeedAnalysis_norm_sq]
  have h := gamma0CompactStonePlancherel_all_atoms N ψ
  have hn : 0≤∑' l : Ici (0:ℝ),‖gamma0AmbientSpectralAtomVector N (gamma0SmoothSeedMass N ψ) (l:ℝ)‖^2 :=
    tsum_nonneg (fun _ => sq_nonneg _)
  linarith only [h,hn]

theorem gamma0EisensteinSeedAnalysis_inner (N : ℕ) [NeZero N] (ψ ξ : h2SmoothCompactSeeds) :
    inner ℂ (gamma0EisensteinSeedAnalysis N ψ) (gamma0EisensteinSeedAnalysis N ξ)=
      gamma0StoneEisensteinPair N ψ ξ := by
  let L := gamma0EisensteinSeedAnalysis N
  let B (x y : h2SmoothCompactSeeds) := inner ℂ (L x) (L y)
  change B ψ ξ=gamma0StoneEisensteinPair N ψ ξ
  apply spectralHermitianPair_eq_of_diagonal B (gamma0StoneEisensteinPair N) _ _ _ _ _ _ _ ψ ξ
  · intro x y z
    simp only [B,map_add,inner_add_right]
  · exact gamma0StoneEisensteinPair_add_right N
  · intro c x y
    simp only [B,map_smul,inner_smul_right]
  · exact gamma0StoneEisensteinPair_smul_right N
  · intro x y
    exact inner_conj_symm (𝕜:=ℂ) (L y) (L x)
  · exact gamma0StoneEisensteinPair_conj N
  · intro x
    rw [gamma0StoneEisensteinPair_diagonal]
    change inner ℂ (L x) (L x)=_
    rw [inner_self_eq_norm_sq_to_K (𝕜:=ℂ)]
    have h := congrArg Complex.ofReal (gamma0EisensteinSeedAnalysis_norm_sq N x)
    rw [Complex.ofReal_pow] at h
    exact h

end ArtinMatthews
