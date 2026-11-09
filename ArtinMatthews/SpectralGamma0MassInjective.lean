module

public import ArtinMatthews.SpectralGamma0CompletedWeakIdentity
public import ArtinMatthews.SpectralModularWeightedTestDensity
public import ArtinMatthews.SpectralGamma0CompactInclusion


set_option backward.privateInPublic true
@[expose] public section

/-! Faithfulness of the actual completed Γ₀ mass-plus-gradient form.
The gradient is forced by the mass through the proved weak identity and
actual compact test separation; injectivity is not an extra form axiom. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups

namespace ArtinMatthews

/-- An actual completed energy vector with zero mass has zero actual
coordinate gradient, hence vanishes in the completed energy norm. -/
theorem gamma0Energy_eq_zero_of_mass_zero (N : ℕ) [NeZero N]
    (u : gamma0EnergySpace N) (hu : gamma0EnergyInclusion N u = 0) : u = 0 := by
  apply gamma0Energy_eq_zero_of_mass_gradient_zero N u hu
  apply gamma0EnergyGradient_eq_zero_of_charts N u
  intro q i
  apply modular_weighted_test_annihilator_eq_zero q.out (gamma0EnergyGradientChart N q i u)
  intro Y hY φ hφ hs hheight hchart
  exact gamma0Energy_gradient_test_zero_of_mass_zero N u hu q hY φ hφ hs hheight
    (fun p hp => ModularGroup.fdo_subset_fd (hchart p hp)) i

/-- The actual completed mass map is injective. In particular no independent
zero-mass gradient vectors occur in the graph closure. -/
theorem gamma0EnergyInclusion_injective (N : ℕ) [NeZero N] :
    Function.Injective (gamma0EnergyInclusion N) := by
  intro u v huv
  apply sub_eq_zero.mp
  apply gamma0Energy_eq_zero_of_mass_zero N (u-v)
  rw [map_sub,huv,sub_self]

/-- The already proved compact all-height mean-zero mass inclusion is also
faithful. This does not assert density in the full cuspidal mass space. -/
theorem gamma0AllHeightMassInclusion_injective (N : ℕ) [NeZero N] :
    Function.Injective (gamma0AllHeightMassInclusion N) := by
  intro u v huv
  apply Subtype.ext
  exact gamma0EnergyInclusion_injective N huv

end ArtinMatthews
