module

public import ArtinMatthews.SpectralGamma0FormOperator
public import ArtinMatthews.SpectralGamma0MassInjective


set_option backward.privateInPublic true
@[expose] public section

/-! Faithfulness of the actual completed energy representation: the weak
derivative closability theorem makes each mass representative unique. -/
noncomputable section
namespace ArtinMatthews

theorem gamma0MassEnergyOperator_unique_energy (N : ℕ) [NeZero N]
    (x y : Gamma0RegionL2 N) :
    (x,y) ∈ (gamma0MassEnergyOperator N).graph ↔ ∃! u : gamma0EnergySpace N,
      gamma0EnergyInclusion N u = x ∧ ∀ v : gamma0EnergySpace N,
        inner ℂ u v = inner ℂ y (gamma0EnergyInclusion N v) := by
  constructor
  · intro h
    obtain ⟨u,hu,hweak⟩ := (gamma0MassEnergyOperator_weak_graph N x y).mp h
    refine ⟨u,⟨hu,hweak⟩,?_⟩
    intro v hv
    exact gamma0EnergyInclusion_injective N (hv.1.trans hu.symm)
  · rintro ⟨u,hu,_⟩
    exact (gamma0MassEnergyOperator_weak_graph N x y).mpr ⟨u,hu⟩

end ArtinMatthews
