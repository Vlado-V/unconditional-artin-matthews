module

public import ArtinMatthews.SpectralBoundedSeedMass
public import ArtinMatthews.SpectralBoundedExponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan


set_option backward.privateInPublic true
@[expose] public section

/-! Entire mass families from fixed compact seeds and bounded logarithms. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported MatrixGroups BoundedContinuousFunction
namespace ArtinMatthews

def gamma0BoundedSeedExponentialMass (N : ℕ) [NeZero N] (ψ : C_c(UpperHalfPlane,ℂ))
    (b : UpperHalfPlane →ᵇ ℂ) (s : ℂ) : Gamma0RegionL2 N :=
  gamma0BoundedSeedMass N ψ (spectralBoundedExponential b s)

theorem gamma0BoundedSeedExponentialMass_analyticAt (N : ℕ) [NeZero N]
    (ψ : C_c(UpperHalfPlane,ℂ)) (b : UpperHalfPlane →ᵇ ℂ) (s : ℂ) :
    AnalyticAt ℂ (gamma0BoundedSeedExponentialMass N ψ b) s :=
  ((gamma0BoundedSeedMass N ψ).analyticAt (spectralBoundedExponential b s)).comp
    (spectralBoundedExponential_analyticAt b s)

theorem gamma0BoundedSeedExponentialMass_ae (N : ℕ) [NeZero N]
    (ψ : C_c(UpperHalfPlane,ℂ)) (b : UpperHalfPlane →ᵇ ℂ) (s : ℂ)
    (q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    (gamma0BoundedSeedExponentialMass N ψ b s q : UpperHalfPlane → ℂ)
      =ᵐ[volume.restrict ModularGroup.fd]
        (fun z => gamma0PoincareSeed N (spectralBoundedSeedProduct ψ (spectralBoundedExponential b s)) (q.out⁻¹ • z)) :=
  gamma0BoundedSeedMass_ae N ψ (spectralBoundedExponential b s) q

end ArtinMatthews
