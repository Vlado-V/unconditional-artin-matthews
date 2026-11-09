module

public import ArtinMatthews.SpectralGamma0CompactInclusion
public import Mathlib.Analysis.InnerProductSpace.ProdL2


set_option backward.privateInPublic true
@[expose] public section

/-! The actual mass closure of the all-positive-height mean-zero energy
space, and its compact dense form inclusion. This is an honest closure
construction; identification with a separately defined full cuspidal L²
space is a further theorem. -/
noncomputable section
open Set Topology
namespace ArtinMatthews

instance gamma0AllHeightMeanZeroEnergy_innerProductSpace (N : ℕ) [NeZero N] :
    InnerProductSpace ℂ (gamma0AllHeightMeanZeroEnergy N) :=
  Submodule.innerProductSpace (𝕜 := ℂ) (E := gamma0EnergySpace N) (gamma0AllHeightMeanZeroEnergy N)

def gamma0AllHeightEnergyMassSpace (N : ℕ) [NeZero N] : Submodule ℂ (Gamma0RegionL2 N) :=
  (gamma0AllHeightMassInclusion N).range.topologicalClosure

instance gamma0AllHeightEnergyMassSpace_innerProductSpace (N : ℕ) [NeZero N] :
    InnerProductSpace ℂ (gamma0AllHeightEnergyMassSpace N) :=
  Submodule.innerProductSpace (𝕜 := ℂ) (E := Gamma0RegionL2 N) (gamma0AllHeightEnergyMassSpace N)

instance gamma0AllHeightEnergyMassSpace_complete (N : ℕ) [NeZero N] :
    CompleteSpace (gamma0AllHeightEnergyMassSpace N) :=
  (Submodule.isClosed_topologicalClosure _).isComplete.completeSpace_coe

def gamma0AllHeightCoreInclusion (N : ℕ) [NeZero N] :
    gamma0AllHeightMeanZeroEnergy N →L[ℂ] gamma0AllHeightEnergyMassSpace N :=
  (gamma0AllHeightMassInclusion N).codRestrict (gamma0AllHeightEnergyMassSpace N)
    (fun u => Submodule.le_topologicalClosure _ ⟨u,rfl⟩)

theorem gamma0AllHeightCoreInclusion_coe (N : ℕ) [NeZero N]
    (u : gamma0AllHeightMeanZeroEnergy N) :
    (gamma0AllHeightCoreInclusion N u).val = gamma0EnergyInclusion N u.val := rfl

theorem gamma0AllHeightCoreInclusion_bound (N : ℕ) [NeZero N]
    (u : gamma0AllHeightMeanZeroEnergy N) : ‖gamma0AllHeightCoreInclusion N u‖ ≤ ‖u‖ :=
  gamma0EnergyInclusion_bound N u.val

theorem gamma0AllHeightCoreInclusion_denseRange (N : ℕ) [NeZero N] :
    DenseRange (gamma0AllHeightCoreInclusion N) := by
  intro u
  rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  have he : Subtype.val '' range (gamma0AllHeightCoreInclusion N) =
      range (gamma0AllHeightMassInclusion N) := by
    ext y
    constructor
    · rintro ⟨v, ⟨w,rfl⟩,rfl⟩
      exact ⟨w,rfl⟩
    · rintro ⟨w,rfl⟩
      exact ⟨gamma0AllHeightCoreInclusion N w, ⟨w,rfl⟩,rfl⟩
  rw [he]
  exact u.property

theorem gamma0AllHeightCoreInclusion_compact (N : ℕ) [NeZero N] :
    IsCompactOperator (gamma0AllHeightCoreInclusion N) :=
  (gamma0AllHeightMassInclusion_compact N).codRestrict
    (V := gamma0AllHeightEnergyMassSpace N)
    (fun u => Submodule.le_topologicalClosure (gamma0AllHeightMassInclusion N).range ⟨u,rfl⟩)
    (Submodule.isClosed_topologicalClosure _)

end ArtinMatthews
