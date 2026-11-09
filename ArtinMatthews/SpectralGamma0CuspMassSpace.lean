module

public import ArtinMatthews.SpectralGamma0CuspMassRestriction
public import ArtinMatthews.SpectralGamma0CompactInclusion


set_option backward.privateInPublic true
@[expose] public section

/-! The actual closed all-positive-height cuspidal mass space.  The condition
is imposed on every cusp and every positive-height strip in the full mass
Hilbert space.  Its energy pullback is proved to be the actual all-height
mean-zero energy domain.  Density of that restricted domain is separate. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups

namespace ArtinMatthews

def gamma0AllHeightCuspidalMassSpace (N : ℕ) [NeZero N] : Submodule ℂ (Gamma0RegionL2 N) :=
  ⨅ (r : SL(2, ℤ)) (Y : {Y : ℝ // 0 < Y}),
    ((cuspHyperbolicAverageProjection (N : ℝ) Y.val Y.property).comp
      (gamma0CuspMassRestriction N r Y.val Y.property)).ker

theorem mem_gamma0AllHeightCuspidalMassSpace_iff (N : ℕ) [NeZero N] (f : Gamma0RegionL2 N) :
    f ∈ gamma0AllHeightCuspidalMassSpace N ↔
      ∀ (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y),
        cuspHyperbolicAverageProjection (N : ℝ) Y hY
          (gamma0CuspMassRestriction N r Y hY f) = 0 := by
  simp only [gamma0AllHeightCuspidalMassSpace, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · exact fun h r Y hY => h r ⟨Y, hY⟩
  · exact fun h r Y => h r Y.val Y.property

theorem gamma0AllHeightCuspidalMassSpace_isClosed (N : ℕ) [NeZero N] :
    IsClosed (gamma0AllHeightCuspidalMassSpace N : Set (Gamma0RegionL2 N)) := by
  unfold gamma0AllHeightCuspidalMassSpace
  simp_rw [Submodule.coe_iInf]
  exact isClosed_iInter fun _ => isClosed_iInter fun _ => ContinuousLinearMap.isClosed_ker _

theorem gamma0SmoothSeedMass_mem_cuspidal_iff (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) :
    gamma0SmoothSeedMass N ψ ∈ gamma0AllHeightCuspidalMassSpace N ↔
      ∀ (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y),
        cuspHyperbolicAverageProjection (N : ℝ) Y hY
          (gamma0CuspHeightSeedLp N r Y hY ψ) = 0 := by
  rw [mem_gamma0AllHeightCuspidalMassSpace_iff]
  simp only [gamma0CuspMassRestriction_apply]

instance gamma0AllHeightCuspidalMassSpace_complete (N : ℕ) [NeZero N] :
    CompleteSpace (gamma0AllHeightCuspidalMassSpace N) :=
  (gamma0AllHeightCuspidalMassSpace_isClosed N).isComplete.completeSpace_coe

/-- Genuine equivalence of the all-height mass condition and the previously
defined all-height energy condition, on the actual completed energy domain. -/
theorem gamma0EnergyInclusion_mem_cuspidalMass_iff (N : ℕ) [NeZero N]
    (u : gamma0EnergySpace N) :
    gamma0EnergyInclusion N u ∈ gamma0AllHeightCuspidalMassSpace N ↔
      u ∈ gamma0AllHeightMeanZeroEnergy N := by
  rw [mem_gamma0AllHeightCuspidalMassSpace_iff, mem_gamma0AllHeightMeanZeroEnergy_iff]
  simp only [gamma0CuspMassRestriction_energy]

theorem gamma0AllHeightCuspidalMassSpace_comap_energy (N : ℕ) [NeZero N] :
    (gamma0AllHeightCuspidalMassSpace N).comap (gamma0EnergyInclusion N).toLinearMap =
      gamma0AllHeightMeanZeroEnergy N := by
  ext u
  exact gamma0EnergyInclusion_mem_cuspidalMass_iff N u

def gamma0AllHeightCuspidalInclusion (N : ℕ) [NeZero N] :
    gamma0AllHeightMeanZeroEnergy N →L[ℂ] gamma0AllHeightCuspidalMassSpace N :=
  (gamma0AllHeightMassInclusion N).codRestrict (gamma0AllHeightCuspidalMassSpace N)
    (fun u => (gamma0EnergyInclusion_mem_cuspidalMass_iff N u.val).mpr u.property)

theorem gamma0AllHeightCuspidalInclusion_coe (N : ℕ) [NeZero N]
    (u : gamma0AllHeightMeanZeroEnergy N) :
    (gamma0AllHeightCuspidalInclusion N u : Gamma0RegionL2 N) =
      gamma0AllHeightMassInclusion N u := rfl

/-- The closure of the actual all-height energy mass image lies in the true
closed all-height mass kernel.  Equality requires restricted-domain density
and is deliberately not inferred from ambient density. -/
theorem gamma0AllHeight_energy_mass_closure_le_cuspidal (N : ℕ) [NeZero N] :
    (gamma0AllHeightMassInclusion N).range.topologicalClosure ≤
      gamma0AllHeightCuspidalMassSpace N := by
  change closure (Set.range (gamma0AllHeightMassInclusion N)) ⊆ _
  apply (gamma0AllHeightCuspidalMassSpace_isClosed N).closure_subset_iff.mpr
  rintro f ⟨u, rfl⟩
  exact (gamma0EnergyInclusion_mem_cuspidalMass_iff N u.val).mpr u.property

end ArtinMatthews
