module

public import ArtinMatthews.SpectralCuspFiniteChartMean
public import ArtinMatthews.SpectralResidualProbeProfile


set_option backward.privateInPublic true
@[expose] public section

/-! The residual eigenspace is genuinely finite dimensional. A fixed
finite family of compact probes is injective on it. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

def gamma0ResidualEnergyEigenspace (N : ℕ) [NeZero N] (l : ℝ) : Submodule ℂ (Gamma0RegionL2 N) :=
  gamma0AmbientEnergyEigenspace N l ⊓ (gamma0AllHeightCuspidalMassSpace N)ᗮ

theorem gamma0ResidualEigen_zero_of_probes (N : ℕ) [NeZero N] (l : ℝ) (hl : 0≤l)
    (m : Gamma0RegionL2 N) (hm : m∈gamma0ResidualEnergyEigenspace N l)
    (hprobe : ∀ i : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
      inner ℂ (gamma0ResidualProbeMass N i.out) m=0) : m=0 := by
  have hcus : m∈gamma0AllHeightCuspidalMassSpace N := by
    rcases le_or_gt (1/4:ℝ) l with hc | hc
    · exact gamma0AmbientEnergyEigenspace_cuspidal_of_critical N l hc m hm.1
    · apply gamma0Mass_cuspidal_of_finiteChart_means_zero N m
      intro i
      obtain ⟨u,hu,hp⟩ := gamma0AmbientEnergyEigenspace_energy_pencil N l hl m hm.1
      let a : ℝ := 1/2+Real.sqrt (1/4-l)
      let s : ℂ := (a:ℂ)
      let q : ℝ := 1-a
      obtain ⟨hs,hspec⟩ := gamma0SubcriticalEigen_parameter hl hc
      have hpu : gamma0EnergyResolventPencil N (s*(1-s)) u=0 := by rw [hspec]; exact hp
      obtain ⟨B,hB⟩ := gamma0EnergyMass_global_outgoing_eigenmode N i.out s hs u hpu
      rw [hu] at hB
      have hq : (q:ℂ)=1-s := by simp only [q,s,Complex.ofReal_sub,Complex.ofReal_one]
      rw [← hq] at hB
      have hzero := gamma0ResidualProbeMass_mode_zero N i.out m q B hB (hprobe i)
      change gamma0GlobalCuspConstantTerm N i.out m=ᵐ[volume.restrict (Ioi 0)] (fun _ => (0:ℂ))
      simpa only [hzero,zero_mul] using hB
  have horth := hm.2 m hcus
  exact inner_self_eq_zero.mp horth

def gamma0ResidualProbeMap (N : ℕ) [NeZero N] (l : ℝ) :
    gamma0ResidualEnergyEigenspace N l →ₗ[ℂ] ((SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) → ℂ) :=
  LinearMap.pi (fun i =>
    (innerSL ℂ (gamma0ResidualProbeMass N i.out)).toLinearMap.comp (gamma0ResidualEnergyEigenspace N l).subtype)

theorem gamma0ResidualProbeMap_injective (N : ℕ) [NeZero N] (l : ℝ) (hl : 0≤l) :
    Function.Injective (gamma0ResidualProbeMap N l) := by
  have hzero (m : gamma0ResidualEnergyEigenspace N l) (hm : gamma0ResidualProbeMap N l m=0) : m=0 := by
    apply Subtype.ext
    apply gamma0ResidualEigen_zero_of_probes N l hl m.val m.property
    intro i
    exact congrArg (fun v => v i) hm
  intro m n hmn
  have hz : gamma0ResidualProbeMap N l (m-n)=0 := by rw [map_sub,hmn,sub_self]
  exact sub_eq_zero.mp (hzero (m-n) hz)

theorem gamma0ResidualEnergyEigenspace_finiteDimensional (N : ℕ) [NeZero N] (l : ℝ) (hl : 0≤l) :
    FiniteDimensional ℂ (gamma0ResidualEnergyEigenspace N l) :=
  FiniteDimensional.of_injective (gamma0ResidualProbeMap N l) (gamma0ResidualProbeMap_injective N l hl)

end ArtinMatthews
