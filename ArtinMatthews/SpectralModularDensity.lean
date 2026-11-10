module

public import ArtinMatthews.SpectralGamma0EnergyGraph
public import ArtinMatthews.SpectralModularDensityAssembly
public import ArtinMatthews.SpectralModularDensitySmooth
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan


set_option backward.privateInPublic true
@[expose] public section

/-!
The actual smooth compact-seed periodizations are dense in the full finite
modular-chart Hilbert space.  Supported smooth density is proved by actual
test-function separation; chart independence and the central `±I` factor are
proved by the modular interior partition.  This realizes the full automorphic
mass space and makes no assertion that a fixed-height mean-zero kernel is the
cuspidal spectrum.
-/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups

namespace ArtinMatthews

/-- The actual compact smooth periodizations generate the entire finite-chart
Hilbert mass space, with no additional compatibility or density premise. -/
theorem gamma0CompactCoreL2_eq_top (N : ℕ) [NeZero N] :
    gamma0CompactCoreL2 N = ⊤ :=
  gamma0CompactCoreL2_eq_top_of_smooth_interior_dense N modular_smooth_compact_supported_dense

/-- Genuine density of the actual smooth-seed mass map in the full modular
chart product. -/
theorem gamma0SmoothSeedMass_denseRange (N : ℕ) [NeZero N] :
    DenseRange (gamma0SmoothSeedMass N) :=
  gamma0SmoothSeedMass_denseRange_of_smooth_interior_dense N
    modular_smooth_compact_supported_dense

/-- The actual completed energy form has dense mass domain in the entire
finite-chart Hilbert space, since it contains every actual smooth seed. -/
theorem gamma0EnergyInclusion_denseRange (N : ℕ) [NeZero N] :
    DenseRange (gamma0EnergyInclusion N) := by
  apply (gamma0SmoothSeedMass_denseRange N).mono
  rintro f ⟨ψ, rfl⟩
  exact ⟨gamma0EnergyTest N ψ, rfl⟩

end ArtinMatthews
