module

public import ArtinMatthews.SpectralEisensteinProfileLaplacian
public import ArtinMatthews.SpectralEisensteinVerticalCutoff


set_option backward.privateInPublic true
@[expose] public section

/-! The literal cutoff has a proved compact radial forcing, represented
by an actual compact-seed Poincaré vector in the full energy space. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups ContDiff
namespace ArtinMatthews

theorem eisensteinVerticalCutoffError_positive_support (s : ℂ) :
    tsupport (eisensteinVerticalCutoffError s) ⊆ Ioi (0:ℝ) :=
  fun _ h => lt_of_lt_of_le (by norm_num) (eisensteinVerticalCutoffError_support s h).1

theorem gamma0CuspEisensteinCutoff_eq_profile (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (z : UpperHalfPlane) :
    gamma0CuspEisensteinCutoff N a s z=
      gamma0CuspHeightProfile N a (eisensteinVerticalCutoffMode s) z := by
  rw [gamma0CuspHeightProfile_eq_tsum N a _ (by norm_num : (0:ℝ)<1)
    (fun t ht => eisensteinVerticalCutoffMode_zero s ht) z]
  rfl

def gamma0CuspEisensteinCompactForcing (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (s : ℂ) :
    UpperHalfPlane → ℂ := gamma0CuspHeightProfile N a (eisensteinVerticalCutoffError s)

def gamma0CuspEisensteinCompactForcingEnergy (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) : gamma0EnergySpace N :=
  gamma0CuspHeightProfileEnergy N a (eisensteinVerticalCutoffError s)
    (eisensteinVerticalCutoffError_smooth s) (eisensteinVerticalCutoffError_compact s)
    (eisensteinVerticalCutoffError_positive_support s)

def gamma0CuspEisensteinCompactForcingMass (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) : Gamma0RegionL2 N :=
  gamma0EnergyInclusion N (gamma0CuspEisensteinCompactForcingEnergy N a s)

theorem gamma0CuspEisensteinCompactForcingMass_ae (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    (gamma0CuspEisensteinCompactForcingMass N a s q : UpperHalfPlane → ℂ)
      =ᵐ[MeasureTheory.volume.restrict ModularGroup.fd]
        (fun z => gamma0CuspEisensteinCompactForcing N a s (q.out⁻¹ • z)) :=
  gamma0CuspHeightProfileEnergy_mass_ae N a (eisensteinVerticalCutoffError s)
    (eisensteinVerticalCutoffError_smooth s) (eisensteinVerticalCutoffError_compact s)
    (eisensteinVerticalCutoffError_positive_support s) q

theorem gamma0CuspEisensteinCompactForcing_eq_poincare (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (z : UpperHalfPlane) :
    gamma0CuspEisensteinCompactForcing N a s z=
      (1/2:ℂ)*gamma0PoincareSeed N
        (cuspHeightProfileSeed N a (eisensteinVerticalCutoffError s)
          (eisensteinVerticalCutoffError_smooth s) (eisensteinVerticalCutoffError_compact s)
          (eisensteinVerticalCutoffError_positive_support s)).val z :=
  gamma0CuspHeightProfile_eq_poincare N a _ _ _ _ z

theorem gamma0CuspEisensteinCutoff_laplacian_error (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (z : UpperHalfPlane) :
    h2SectionPositiveLaplacian (gamma0CuspEisensteinCutoff N a s) z-
      s*(1-s)*gamma0CuspEisensteinCutoff N a s z=
        gamma0CuspEisensteinCompactForcing N a s z := by
  have he : gamma0CuspEisensteinCutoff N a s=
      gamma0CuspHeightProfile N a (eisensteinVerticalCutoffMode s) :=
    funext (gamma0CuspEisensteinCutoff_eq_profile N a s)
  rw [he]
  exact gamma0CuspHeightProfile_laplacian_error N a (eisensteinVerticalCutoffMode s)
    (eisensteinVerticalCutoffMode_smooth s) (by norm_num : (0:ℝ)<1)
    (fun t ht => eisensteinVerticalCutoffMode_zero s ht) (s*(1-s)) z

end ArtinMatthews
