module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import ArtinMatthews.SpectralGamma0Core
public import Mathlib.MeasureTheory.Function.L2Space
public import ArtinMatthews.SpectralGamma0EnergyPairing
public import ArtinMatthews.SpectralModularDensityPeriodization
public import ArtinMatthews.SpectralPoincareUnfolding
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


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
