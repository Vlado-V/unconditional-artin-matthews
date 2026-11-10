module

public import ArtinMatthews.SpectralGamma0EnergyGraph
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan


set_option backward.privateInPublic true
@[expose] public section

/-! Density and the actual mass-space codomain of the Γ₀ energy completion. -/

noncomputable section
open Set Topology

namespace ArtinMatthews

/-- The generating map as an actual complex linear map. -/
def gamma0EnergyTestLinear (N : ℕ) [NeZero N] :
    h2SmoothCompactSeeds →ₗ[ℂ] gamma0EnergySpace N :=
  (gamma0EnergyGraph N).codRestrict (gamma0EnergySpace N)
    (fun ψ => Submodule.le_topologicalClosure _ ⟨ψ, rfl⟩)

/-- Density follows from the actual graph closure, with its subtype topology. -/
theorem gamma0EnergyTest_dense (N : ℕ) [NeZero N] : DenseRange (gamma0EnergyTestLinear N) := by
  intro u
  rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  have he : Subtype.val '' range (gamma0EnergyTestLinear N) = range (gamma0EnergyGraph N) := by
    ext y
    constructor
    · rintro ⟨v, ⟨ψ, rfl⟩, rfl⟩
      exact ⟨ψ, rfl⟩
    · rintro ⟨ψ, rfl⟩
      exact ⟨gamma0EnergyTestLinear N ψ, ⟨ψ, rfl⟩, rfl⟩
  rw [he]
  exact u.property

/-- No extraneous mass vectors appear on completing the actual energy graph. -/
theorem gamma0EnergyInclusion_mem_core (N : ℕ) [NeZero N] (u : gamma0EnergySpace N) :
    gamma0EnergyInclusion N u ∈ gamma0CompactCoreL2 N := by
  apply isClosed_property (gamma0EnergyTest_dense N)
    ((Submodule.isClosed_topologicalClosure _).preimage (gamma0EnergyInclusion N).continuous)
  intro ψ
  exact gamma0SmoothSeedMass_mem_core N ψ

/-- The mass inclusion into its actual closed smooth-core Hilbert space. -/
def gamma0CoreEnergyInclusion (N : ℕ) [NeZero N] :
    gamma0EnergySpace N →L[ℂ] gamma0CompactCoreL2 N :=
  (gamma0EnergyInclusion N).codRestrict (gamma0CompactCoreL2 N)
    (gamma0EnergyInclusion_mem_core N)

theorem gamma0CoreEnergyInclusion_norm_le (N : ℕ) [NeZero N] (u : gamma0EnergySpace N) :
    ‖gamma0CoreEnergyInclusion N u‖ ≤ ‖u‖ := gamma0EnergyInclusion_bound N u

/-- The completed inclusion has dense range in the actual constructed mass
space.  This does not identify that space with all automorphic L² functions. -/
theorem gamma0CoreEnergyInclusion_dense (N : ℕ) [NeZero N] :
    DenseRange (gamma0CoreEnergyInclusion N) := by
  intro u
  rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  apply closure_mono ?_ u.property
  rintro y ⟨ψ, rfl⟩
  exact ⟨gamma0CoreEnergyInclusion N (gamma0EnergyTest N ψ),
    ⟨gamma0EnergyTest N ψ, rfl⟩, rfl⟩

end ArtinMatthews
