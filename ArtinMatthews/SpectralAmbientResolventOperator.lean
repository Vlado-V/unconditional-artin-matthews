module

public import ArtinMatthews.SpectralGamma0AmbientResolventAnalytic


set_option backward.privateInPublic true
@[expose] public section

/-! The constructed full ambient weak resolvent is the actual resolvent
of the existing self-adjoint mass-plus-energy operator. -/
noncomputable section
namespace ArtinMatthews

theorem gamma0AmbientResolvent_operator_graph (N : ℕ) [NeZero N] (z : ℂ)
    (hz : z.re < ‖z‖) (F : Gamma0RegionL2 N) :
    (gamma0AmbientResolvent N z hz F,
      F+(z+1) • gamma0AmbientResolvent N z hz F) ∈ (gamma0MassEnergyOperator N).graph := by
  let U := gamma0AmbientWeakResolvent N z hz F
  let X := gamma0AmbientResolvent N z hz F
  have hp := gamma0AmbientWeakResolvent_pencil N z hz F
  change U-(z+1) • gamma0EnergyMassAdjoint N X=gamma0EnergyMassAdjoint N F at hp
  have he : gamma0EnergyMassAdjoint N (F+(z+1) • X)=U := by
    rw [map_add,map_smul,← hp,sub_add_cancel]
  apply (gamma0MassEnergyOperator_graph N X (F+(z+1) • X)).mpr
  change gamma0EnergyInclusion N (gamma0EnergyMassAdjoint N (F+(z+1) • X))=X
  rw [he]
  rfl

theorem gamma0AmbientResolventFamily_operator_graph (N : ℕ) [NeZero N] (z : ℂ)
    (hz : z.re < ‖z‖) (F : Gamma0RegionL2 N) :
    (gamma0AmbientResolventFamily N z F,F+(z+1) • gamma0AmbientResolventFamily N z F)
      ∈ (gamma0MassEnergyOperator N).graph := by
  rw [gamma0AmbientResolventFamily_eq N z hz]
  exact gamma0AmbientResolvent_operator_graph N z hz F

end ArtinMatthews
