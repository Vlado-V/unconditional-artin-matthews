module

public import ArtinMatthews.SpectralModularDensitySeeds
public import ArtinMatthews.SpectralGamma0CuspGraphCore
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import ArtinMatthews.SpectralGamma0CompactMass
public import ArtinMatthews.SpectralGamma0GlobalPairing
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

/-! Exact cusp-translated smooth-seed mass unfolding. The actual compact
smooth pullback is reused, and the variable change is with the genuine
invariant hyperbolic volume. The central multiplicity remains two. -/
namespace ArtinMatthews
noncomputable section
open Set MeasureTheory Filter
open scoped CompactlySupported MatrixGroups InnerProductSpace

/-- A compact test pairs integrably with an actual continuous section. -/
theorem h2_compactSeed_inner_integrable (ψ : h2SmoothCompactSeeds)
    (F : UpperHalfPlane → ℂ) (hF : Continuous F) :
    Integrable (fun z => inner ℂ (ψ.val z) (F z)) (volume : Measure UpperHalfPlane) := by
  apply (ψ.val.continuous.inner hF).integrable_of_hasCompactSupport
  apply ψ.val.hasCompactSupport.mono'
  intro z hz
  by_contra hout
  have hzero : ψ.val z = 0 := image_eq_zero_of_notMem_tsupport hout
  exact hz (by change inner ℂ (ψ.val z) (F z) = 0; rw [hzero, inner_zero_left])

/-- The literal translated test `ψ(r z)` pairs with the literal inverse
pullback `F(r⁻¹ z)`, with no unproved automorphic representative involved. -/
theorem h2_compactSeed_inner_modularTranslate (r : SL(2, ℤ))
    (ψ : h2SmoothCompactSeeds) (F : UpperHalfPlane → ℂ) :
    (∫ z : UpperHalfPlane, inner ℂ ((modularTranslateSmoothSeed r ψ).val z) (F z)) =
      ∫ z : UpperHalfPlane, inner ℂ (ψ.val z) (F (r⁻¹ • z)) := by
  have hme : MeasurableEmbedding (fun z : UpperHalfPlane => r • z) := by
    change MeasurableEmbedding (fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ r • z)
    exact measurableEmbedding_const_smul _
  simpa only [modularTranslateSmoothSeed_apply, inv_smul_smul] using
    (h2_integer_measurePreserving r).integral_comp hme
      (fun z : UpperHalfPlane => inner ℂ (ψ.val z) (F (r⁻¹ • z)))

/-- The actual smooth cusp-section pairing is absolutely integrable. -/
theorem cuspSmoothSeed_pairing_integrable (N : ℕ) [NeZero N]
    (ψ φ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) :
    Integrable (fun z : UpperHalfPlane => inner ℂ (ψ.val z) (gamma0CuspSection N φ r z)) volume := by
  apply h2_compactSeed_inner_integrable ψ
  exact (gamma0PoincareSeed N φ.val).continuous.comp
    (continuous_const_smul (Matrix.SpecialLinearGroup.mapGL ℝ r⁻¹))

/-- Exact smooth Γ₀-region L² unfolding at any integral cusp. The seed is
pulled back by `r` and the actual cusp section is pulled back by `r⁻¹`.
The proved central multiplicity is the genuine factor two. -/
theorem gamma0SmoothSeedMass_inner_unfold_translated (N : ℕ) [NeZero N]
    (ψ φ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) :
    inner ℂ (gamma0SmoothSeedMass N (modularTranslateSmoothSeed r ψ))
      (gamma0SmoothSeedMass N φ) =
      2 * ∫ z : UpperHalfPlane, inner ℂ (ψ.val z) (gamma0CuspSection N φ r z) := by
  rw [gamma0SmoothSeedMass_inner_unfold,
    h2_compactSeed_inner_modularTranslate r ψ (gamma0PoincareSeed N φ.val)]
  rfl

end
end ArtinMatthews
