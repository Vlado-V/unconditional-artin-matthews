module

public import ArtinMatthews.SpectralGamma0CuspFormOperator
public import ArtinMatthews.SpectralGamma0MassInjective


set_option backward.privateInPublic true
@[expose] public section

/-! Faithful energy representatives for the actual all-height form operator. -/
noncomputable section
namespace ArtinMatthews

local instance cuspFormFaithful_energyInner (N : ℕ) [NeZero N] : Inner ℂ (gamma0AllHeightMeanZeroEnergy N) :=
  (gamma0AllHeightMeanZeroEnergy_innerProductSpace N).toInner
local instance cuspFormFaithful_massInner (N : ℕ) [NeZero N] : Inner ℂ (gamma0AllHeightEnergyMassSpace N) :=
  (gamma0AllHeightEnergyMassSpace_innerProductSpace N).toInner

theorem gamma0AllHeightCoreInclusion_injective (N : ℕ) [NeZero N] :
    Function.Injective (gamma0AllHeightCoreInclusion N) := by
  intro u v h
  exact gamma0AllHeightMassInclusion_injective N (congrArg Subtype.val h)

theorem gamma0AllHeightMassEnergyOperator_unique_energy (N : ℕ) [NeZero N]
    (x y : gamma0AllHeightEnergyMassSpace N) :
    (x,y) ∈ (gamma0AllHeightMassEnergyOperator N).graph ↔ ∃! u : gamma0AllHeightMeanZeroEnergy N,
      gamma0AllHeightCoreInclusion N u = x ∧ ∀ v : gamma0AllHeightMeanZeroEnergy N,
        inner ℂ u v = inner ℂ y (gamma0AllHeightCoreInclusion N v) := by
  constructor
  · intro h
    obtain ⟨u,hu,hweak⟩ := (gamma0AllHeightMassEnergyOperator_weak_graph N x y).mp h
    refine ⟨u,⟨hu,hweak⟩,?_⟩
    intro v hv
    exact gamma0AllHeightCoreInclusion_injective N (hv.1.trans hu.symm)
  · rintro ⟨u,hu,_⟩
    exact (gamma0AllHeightMassEnergyOperator_weak_graph N x y).mpr ⟨u,hu⟩

end ArtinMatthews
