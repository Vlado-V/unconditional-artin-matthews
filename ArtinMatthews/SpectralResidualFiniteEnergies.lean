module

public import ArtinMatthews.SpectralResidualEigenspaceFinite
public import ArtinMatthews.SpectralStoneResidualPair


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine residual eigenenergies belong to one fixed finite compact
exceptional set, obtained from a common cutoff for all translated probes. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

def gamma0ResidualRegularEnergy (N : ℕ) [NeZero N] : Set ℝ :=
  gamma0StoneGoodEnergy N (gamma0ResidualProbeSeed N) (gamma0ResidualProbeCutoff N)

def gamma0ResidualEnergyCandidates (N : ℕ) [NeZero N] : Set ℝ :=
  Icc (0:ℝ) (1/4)\gamma0ResidualRegularEnergy N

theorem gamma0ResidualEnergyCandidates_finite (N : ℕ) [NeZero N] :
    (gamma0ResidualEnergyCandidates N).Finite :=
  gamma0StoneGoodEnergy_finite_compl_on_compact N (gamma0ResidualProbeSeed N)
    (gamma0ResidualProbeCutoff N) isCompact_Icc

theorem gamma0ResidualProbe_pairing_zero_of_regular (N : ℕ) [NeZero N]
    (l : ℝ) (hl : 0≤l) (hr : l∈gamma0ResidualRegularEnergy N)
    (r : SL(2,ℤ)) (m : Gamma0RegionL2 N) (hm : m∈gamma0AmbientEnergyEigenspace N l) :
    inner ℂ (gamma0ResidualProbeMass N r) m=0 := by
  let ψ := modularTranslateSmoothSeed r (gamma0ResidualProbeSeed N)
  let A := (gamma0ResidualProbeCutoff N).modularTranslate r
  have hreg : l∈gamma0StoneGoodEnergy N ψ A := hr
  have hz := gamma0CompactStoneAtom_zero_of_good N ψ A l hl hreg
  have h := gamma0AmbientSpectralAtomVector_orthogonal N (gamma0SmoothSeedMass N ψ) m l
    ((mem_gamma0AmbientEnergyEigenspace_iff N l m).mp hm)
  rw [hz,sub_zero] at h
  exact inner_eq_zero_symm.mpr h

theorem gamma0ResidualEigen_zero_of_not_mem_candidates (N : ℕ) [NeZero N]
    (l : ℝ) (hl : 0≤l) (hn : l∉gamma0ResidualEnergyCandidates N)
    (m : Gamma0RegionL2 N) (hm : m∈gamma0ResidualEnergyEigenspace N l) : m=0 := by
  rcases le_or_gt (1/4:ℝ) l with hc | hc
  · have hcus := gamma0AmbientEnergyEigenspace_cuspidal_of_critical N l hc m hm.1
    exact inner_self_eq_zero.mp (hm.2 m hcus)
  · have hreg : l∈gamma0ResidualRegularEnergy N := by
      by_contra h
      exact hn ⟨⟨hl,hc.le⟩,h⟩
    exact gamma0ResidualEigen_zero_of_probes N l hl m hm
      (fun i => gamma0ResidualProbe_pairing_zero_of_regular N l hl hreg i.out m hm.1)

theorem gamma0AmbientResidualProjection_mem (N : ℕ) [NeZero N] (l : ℝ) (u : Gamma0RegionL2 N) :
    gamma0AmbientResidualProjection N l u∈gamma0ResidualEnergyEigenspace N l := by
  rw [gamma0AmbientResidualProjection_eq]
  constructor
  · exact gamma0NoncuspidalRemainder_ambient_eigen N l _ ((mem_gamma0AmbientEnergyEigenspace_iff N l _).mpr
      (gamma0AmbientSpectralAtomVector_green N u l))
  · intro w hw
    exact inner_eq_zero_symm.mpr (gamma0NoncuspidalRemainder_orthogonal N _ ⟨w,hw⟩)

theorem gamma0AmbientResidualProjection_zero_off_finite (N : ℕ) [NeZero N]
    (l : ℝ) (hl : 0≤l) (hn : l∉gamma0ResidualEnergyCandidates N) (u : Gamma0RegionL2 N) :
    gamma0AmbientResidualProjection N l u=0 :=
  gamma0ResidualEigen_zero_of_not_mem_candidates N l hl hn _ (gamma0AmbientResidualProjection_mem N l u)

end ArtinMatthews
