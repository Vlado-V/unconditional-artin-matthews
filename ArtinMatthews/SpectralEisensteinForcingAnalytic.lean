module

public import ArtinMatthews.SpectralEisensteinForcingSeeds


set_option backward.privateInPublic true
@[expose] public section

/-! Entire dependence of the actual compact Eisenstein forcing in the full
ambient L² space, via its proved fixed-seed decomposition. -/
noncomputable section
open scoped MatrixGroups CompactlySupported
namespace ArtinMatthews

def gamma0EisensteinForcingAnalyticFamily (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (s : ℂ) :
    Gamma0RegionL2 N :=
  (1/2:ℂ) • (gamma0BoundedSeedExponentialMass N (gamma0EisensteinForcingSeed0 N a).val
    (gamma0SourceBoundedLog N a) s+
    s • gamma0BoundedSeedExponentialMass N (gamma0EisensteinForcingSeed1 N a).val
      (gamma0SourceBoundedLog N a) s)

theorem gamma0CuspEisensteinCompactForcingMass_eq_analytic (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) :
    gamma0CuspEisensteinCompactForcingMass N a s=gamma0EisensteinForcingAnalyticFamily N a s := by
  change gamma0SeedMass N ((1/2:ℂ) •
    (cuspHeightProfileSeed N a (eisensteinVerticalCutoffError s)
      (eisensteinVerticalCutoffError_smooth s) (eisensteinVerticalCutoffError_compact s)
      (eisensteinVerticalCutoffError_positive_support s)).val)=_
  rw [map_smul,gamma0EisensteinForcingSeed_decomposition,map_add,map_smul]
  rfl

theorem gamma0CuspEisensteinCompactForcingMass_analyticAt (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) : AnalyticAt ℂ (gamma0CuspEisensteinCompactForcingMass N a) s := by
  have he : gamma0CuspEisensteinCompactForcingMass N a=gamma0EisensteinForcingAnalyticFamily N a :=
    funext (gamma0CuspEisensteinCompactForcingMass_eq_analytic N a)
  rw [he]
  have h0 := gamma0BoundedSeedExponentialMass_analyticAt N (gamma0EisensteinForcingSeed0 N a).val
    (gamma0SourceBoundedLog N a) s
  have h1 := gamma0BoundedSeedExponentialMass_analyticAt N (gamma0EisensteinForcingSeed1 N a).val
    (gamma0SourceBoundedLog N a) s
  exact (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (1/2:ℂ)) s).smul
    (h0.add ((analyticAt_id : AnalyticAt ℂ (fun z : ℂ => z) s).smul h1))

end ArtinMatthews
