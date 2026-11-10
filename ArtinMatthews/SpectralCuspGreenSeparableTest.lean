module

public import ArtinMatthews.SpectralCuspSeparableSupport
public import ArtinMatthews.SpectralCuspTwoCellHyperbolic
public import ArtinMatthews.SpectralGamma0WeakInverse
public import ArtinMatthews.SpectralCuspCompletedUnfolding
public import ArtinMatthews.SpectralGamma0GlobalWeakLaplacian
public import ArtinMatthews.SpectralSectionLaplacianPullback
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
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
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

/-! The actual ambient Green equation tested by the genuine period-window
seed in any cusp, unfolded against the bounded completed two-cell field. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace

namespace ArtinMatthews

theorem gamma0Green_twoCell_separable_weak_laplacian (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hρpos : tsupport ρ ⊆ Ioi (0 : ℝ)) (hs : tsupport ρ ⊆ Ioi Y)
    (f : Gamma0RegionL2 N) :
    let ψ := cuspConstantTermTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) ρ hρ hρc hρpos
    (∫ z in hyperbolicCuspStrip (2 * (N : ℝ)) Y,
      inner ℂ (ψ.val z) (gamma0CuspTwoCellMassRestriction N r Y hY (gamma0Green N f) z)) +
    (∫ z in hyperbolicCuspStrip (2 * (N : ℝ)) Y,
      inner ℂ ((h2SectionLaplacianSeed ψ).val z)
        (gamma0CuspTwoCellMassRestriction N r Y hY (gamma0Green N f) z)) =
    ∫ z in hyperbolicCuspStrip (2 * (N : ℝ)) Y,
      inner ℂ (ψ.val z) (gamma0CuspTwoCellMassRestriction N r Y hY f z) := by
  let ψ := cuspConstantTermTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) ρ hρ hρc hρpos
  have hψ := cuspConstantTermTestSeed_support (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N))
    ρ hρ hρc hρpos Y hs
  have hΔψ := cuspConstantTermTestSeed_laplacian_support (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N))
    ρ hρ hρc hρpos Y hs
  have he := gamma0Green_global_weak_laplacian N (modularTranslateSmoothSeed r ψ) f
  rw [h2SectionLaplacianSeed_modular_pullback, inner_add_left,
    gamma0Mass_inner_unfold_twoCell_integral N r Y hY ψ hψ (gamma0Green N f),
    gamma0Mass_inner_unfold_twoCell_integral N r Y hY (h2SectionLaplacianSeed ψ) hΔψ (gamma0Green N f),
    gamma0Mass_inner_unfold_twoCell_integral N r Y hY ψ hψ f] at he
  apply mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)
  simpa only [mul_add] using he

end ArtinMatthews
