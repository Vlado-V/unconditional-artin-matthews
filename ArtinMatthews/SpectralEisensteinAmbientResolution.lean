module

public import ArtinMatthews.SpectralEisensteinAnalysisCompletion
public import ArtinMatthews.SpectralResidualEigenbasis


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine Eisenstein analysis and finite residual projections
resolve every ambient mass vector. The synthesis is the actual Hilbert
adjoint of the densely calibrated Eisenstein transform. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

local instance eisensteinAmbient_cuspInner (N : ℕ) [NeZero N] :
    InnerProductSpace ℂ (gamma0AllHeightCuspidalMassSpace N) :=
  Submodule.innerProductSpace (𝕜:=ℂ) (E:=Gamma0RegionL2 N) (gamma0AllHeightCuspidalMassSpace N)

def gamma0ResidualProjection (N : ℕ) [NeZero N] :
    Gamma0RegionL2 N →L[ℂ] Gamma0RegionL2 N :=
  ∑ l∈gamma0ResidualEnergyWindow N,gamma0AmbientResidualProjection N (l:ℝ)

theorem gamma0ResidualProjection_inner (N : ℕ) [NeZero N] (f g : Gamma0RegionL2 N) :
    inner ℂ f (gamma0ResidualProjection N g)=gamma0StoneResidualPair N f g := by
  have hterm (l : Ici (0:ℝ)) :
      inner ℂ f (gamma0AmbientResidualProjection N l g)=
        inner ℂ (gamma0AmbientResidualProjection N l f) (gamma0AmbientResidualProjection N l g) := by
    let K := gamma0ResidualEnergyEigenspace N l
    let p := K.orthogonalProjectionOnto g
    have hp : p.val=gamma0AmbientResidualProjection N l g :=
      (gamma0AmbientResidualProjection_eq_orthogonalProjection N l g).symm
    have h := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right p f
    change inner ℂ (K.starProjection f) p.val=inner ℂ f p.val at h
    rw [hp,← gamma0AmbientResidualProjection_eq_orthogonalProjection N l f] at h
    exact h.symm
  rw [gamma0ResidualProjection,sum_apply,inner_sum]
  simp_rw [hterm]
  exact (gamma0StoneResidualPair_eq_finite N f g).symm

theorem gamma0AmbientEisenstein_spectral_pairing (N : ℕ) [NeZero N] (f g : Gamma0RegionL2 N) :
    inner ℂ f g=
      inner ℂ (gamma0CuspidalProjection N f) (gamma0CuspidalProjection N g)+
      (inner ℂ (gamma0EisensteinAnalysis N f) (gamma0EisensteinAnalysis N g)+
        inner ℂ f (gamma0ResidualProjection N g)) := by
  have hleft : Continuous (fun p : Gamma0RegionL2 N × Gamma0RegionL2 N => inner ℂ p.1 p.2) :=
    continuous_fst.inner continuous_snd
  have hright : Continuous (fun p : Gamma0RegionL2 N × Gamma0RegionL2 N =>
      inner ℂ (gamma0CuspidalProjection N p.1) (gamma0CuspidalProjection N p.2)+
      (inner ℂ (gamma0EisensteinAnalysis N p.1) (gamma0EisensteinAnalysis N p.2)+
        inner ℂ p.1 (gamma0ResidualProjection N p.2))) :=
    (((gamma0CuspidalProjection N).continuous.comp continuous_fst).inner
      ((gamma0CuspidalProjection N).continuous.comp continuous_snd)).add
      ((((gamma0EisensteinAnalysis N).continuous.comp continuous_fst).inner
        ((gamma0EisensteinAnalysis N).continuous.comp continuous_snd)).add
        (continuous_fst.inner ((gamma0ResidualProjection N).continuous.comp continuous_snd)))
  apply isClosed_property2 (p:=fun x y : Gamma0RegionL2 N =>
    inner ℂ x y=inner ℂ (gamma0CuspidalProjection N x) (gamma0CuspidalProjection N y)+
      (inner ℂ (gamma0EisensteinAnalysis N x) (gamma0EisensteinAnalysis N y)+
        inner ℂ x (gamma0ResidualProjection N y)))
    (gamma0SmoothSeedMass_denseRange N) (isClosed_eq hleft hright)
  intro ψ ξ
  rw [gamma0_mass_cuspidal_split N,gamma0CompactStoneNoncuspidalPairing N ψ ξ,
    gamma0EisensteinAnalysis_compact_pair N ψ ξ,gamma0ResidualProjection_inner]

theorem gamma0AmbientEisenstein_resolution (N : ℕ) [NeZero N] (f : Gamma0RegionL2 N) :
    f=(gamma0CuspidalProjection N f).val+gamma0ResidualProjection N f+
      (gamma0EisensteinAnalysis N).adjoint (gamma0EisensteinAnalysis N f) := by
  apply ext_inner_left ℂ
  intro g
  rw [inner_add_right,inner_add_right,ContinuousLinearMap.adjoint_inner_right]
  have h := gamma0AmbientEisenstein_spectral_pairing N g f
  rw [gamma0CuspidalProjection_inner_right N g (gamma0CuspidalProjection N f)] at h
  linear_combination h

theorem gamma0EisensteinSynthesis_compact_pair (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (v : Gamma0EisensteinSpectralSpace N) :
    inner ℂ (gamma0SmoothSeedMass N ψ) ((gamma0EisensteinAnalysis N).adjoint v)=
      inner ℂ (gamma0EisensteinSeedAnalysis N ψ) v := by
  rw [ContinuousLinearMap.adjoint_inner_right,gamma0EisensteinAnalysis_seed]

end ArtinMatthews
