module

public import ArtinMatthews.SpectralPoincareUnfolding
public import ArtinMatthews.SpectralGamma0EnergyPairing
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions


set_option backward.privateInPublic true
@[expose] public section

/-! The exact complex mass pairing of actual periodizations unfolds with
the proved central multiplicity two. -/

noncomputable section
open Set MeasureTheory
open scoped CompactlySupported MatrixGroups InnerProductSpace

namespace ArtinMatthews

theorem gamma0PoincareSeed_star (N : ℕ) [NeZero N]
    (ψ : C_c(UpperHalfPlane, ℂ)) (z : UpperHalfPlane) :
    gamma0PoincareSeed N (star ψ) z = star (gamma0PoincareSeed N ψ z) := by
  rw [gamma0PoincareSeed_eq_finsum,gamma0PoincareSeed_eq_finsum]
  simpa only [CompactlySupportedContinuousMap.star_apply,starAddEquiv_apply] using
    ((starAddEquiv : ℂ ≃+ ℂ).map_finsum
      (fun γ : CongruenceSubgroup.Gamma0 N => ψ ((γ : SL(2, ℤ)) • z))).symm

theorem gamma0_periodization_unfold_inner (N : ℕ) [NeZero N]
    (F : UpperHalfPlane → ℂ) (hF : Continuous F)
    (hFinv : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane,
      F ((γ : SL(2, ℤ)) • z) = F z)
    (ψ : C_c(UpperHalfPlane, ℂ)) :
    (∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
      ∫ z in ModularGroup.fd, inner ℂ (gamma0PoincareSeed N ψ (q.out⁻¹ • z))
        (F (q.out⁻¹ • z))) =
      2 * ∫ z : UpperHalfPlane, inner ℂ (ψ z) (F z) := by
  simpa only [gamma0PoincareSeed_star,CompactlySupportedContinuousMap.star_apply,
    RCLike.inner_apply,starRingEnd_apply] using
      gamma0_periodization_unfold_integral N F hF hFinv (star ψ)

theorem gamma0SmoothSeedMass_inner_unfold (N : ℕ) [NeZero N]
    (ψ φ : h2SmoothCompactSeeds) :
    inner ℂ (gamma0SmoothSeedMass N ψ) (gamma0SmoothSeedMass N φ) =
      2 * ∫ z : UpperHalfPlane, inner ℂ (ψ.val z) (gamma0PoincareSeed N φ.val z) := by
  rw [gamma0SmoothSeedMass_inner]
  exact gamma0_periodization_unfold_inner N (gamma0PoincareSeed N φ.val)
    (gamma0PoincareSeed N φ.val).continuous (gamma0PoincareSeed_invariant N φ.val) ψ.val

end ArtinMatthews
