module

public import ArtinMatthews.SpectralL2PointwiseIdentification
public import ArtinMatthews.SpectralEisensteinMassApproximation
public import ArtinMatthews.SpectralCuspConstantTermRepresentative


set_option backward.privateInPublic true
@[expose] public section

/-! The actual initial Eisenstein remainder is the almost-everywhere
representative of its genuine completed cusp restriction. This follows
from proved compact-core approximation and strong mass convergence. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped MatrixGroups ContDiff
namespace ArtinMatthews

theorem gamma0CuspHeightProfileEnergy_restriction_ae (N : ℕ) [NeZero N]
    (r a : SL(2,ℤ)) (ρ : ℝ → ℂ) (hρ : ContDiff ℝ ∞ ρ)
    (hρc : HasCompactSupport ρ) (hpos : tsupport ρ ⊆ Ioi (0:ℝ))
    (Y : ℝ) (hY : 0<Y) :
    gamma0CuspMassRestriction N r Y hY
      (gamma0EnergyInclusion N (gamma0CuspHeightProfileEnergy N a ρ hρ hρc hpos))
      =ᵐ[volume.restrict (hyperbolicCuspStrip (N:ℝ) Y)]
        fun z => gamma0CuspHeightProfile N a ρ (r⁻¹ • z) := by
  let ψ := cuspHeightProfileSeed N a ρ hρ hρc hpos
  have he := gamma0CuspMassRestriction_seed_ae N r Y hY ((1/2:ℂ) • ψ)
  refine he.trans (Eventually.of_forall fun z => ?_)
  change gamma0CuspSection N ((1/2:ℂ) • ψ) r z=gamma0CuspHeightProfile N a ρ (r⁻¹ • z)
  rw [gamma0CuspHeightProfile_eq_poincare N a ρ hρ hρc hpos]
  change arithmeticPoincareSeed (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
    ((1/2:ℂ) • ψ.val) (r⁻¹ • z)=_
  rw [arithmeticPoincareSeed_smul]
  rfl

theorem gamma0CuspEisensteinRemainderMass_restriction_ae (N : ℕ) [NeZero N]
    (r a : SL(2,ℤ)) (s : ℂ) (hs : 1<s.re) (Y : ℝ) (hY : 0<Y) :
    gamma0CuspMassRestriction N r Y hY (gamma0CuspEisensteinRemainderMass N a s hs)
      =ᵐ[volume.restrict (hyperbolicCuspStrip (N:ℝ) Y)]
        fun z => gamma0CuspEisensteinRemainder N a s (r⁻¹ • z) := by
  apply spectralL2_ae_eq_of_tendsto_pointwise
    (volume.restrict (hyperbolicCuspStrip (N:ℝ) Y))
    (fun n => gamma0CuspMassRestriction N r Y hY
      (gamma0EnergyInclusion N (gamma0CuspEisensteinApproxEnergy N a s n))) _
    (fun n z => gamma0CuspHeightProfile N a (eisensteinRadialApprox s (n+1:ℕ)) (r⁻¹ • z)) _
    ((gamma0CuspMassRestriction N r Y hY).continuous.tendsto _ |>.comp
      (gamma0CuspEisensteinApproxEnergy_mass_tendsto N a s hs))
  · intro n
    exact gamma0CuspHeightProfileEnergy_restriction_ae N r a _
      (eisensteinRadialApprox_smooth s (by positivity))
      (eisensteinRadialApprox_compact s (by positivity))
      (eisensteinRadialApprox_positive_support s (by positivity)) Y hY
  · exact Eventually.of_forall fun z => gamma0CuspEisensteinRadialApprox_tendsto N a s hs (r⁻¹ • z)

end ArtinMatthews
