module

public import ArtinMatthews.SpectralCuspTwoCellHyperbolic
public import ArtinMatthews.SpectralGamma0WeakInverse
public import ArtinMatthews.SpectralSectionLaplacian
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
public import Mathlib.Order.CompletePartialOrder
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

/-! The true ambient Green equation on every compact test in an actual
positive-height two-cell cusp patch.  No regularity of the L² datum is assumed. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups InnerProductSpace

namespace ArtinMatthews

theorem gamma0Green_twoCell_compact_weak_laplacian (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (ψ : h2SmoothCompactSeeds)
    (hs : tsupport ψ.val ⊆ hyperbolicCuspStrip (2*(N : ℝ)) Y) (f : Gamma0RegionL2 N) :
    (∫ z in hyperbolicCuspStrip (2*(N : ℝ)) Y,
      inner ℂ (ψ.val z) (gamma0CuspTwoCellMassRestriction N r Y hY (gamma0Green N f) z)) +
    (∫ z in hyperbolicCuspStrip (2*(N : ℝ)) Y,
      inner ℂ (h2SectionPositiveLaplacian ψ.val z)
        (gamma0CuspTwoCellMassRestriction N r Y hY (gamma0Green N f) z)) =
    ∫ z in hyperbolicCuspStrip (2*(N : ℝ)) Y,
      inner ℂ (ψ.val z) (gamma0CuspTwoCellMassRestriction N r Y hY f z) := by
  have hψ : Function.support (fun z => ψ.val z) ⊆ hyperbolicCuspStrip (2*(N : ℝ)) Y :=
    (subset_tsupport _).trans hs
  have hΔψ : Function.support (fun z => (h2SectionLaplacianSeed ψ).val z) ⊆
      hyperbolicCuspStrip (2*(N : ℝ)) Y :=
    (subset_tsupport _).trans ((h2SectionPositiveLaplacian_tsupport_subset ψ).trans hs)
  have he := gamma0Green_global_weak_laplacian N (modularTranslateSmoothSeed r ψ) f
  rw [h2SectionLaplacianSeed_modular_pullback,inner_add_left,
    gamma0Mass_inner_unfold_twoCell_integral N r Y hY ψ hψ (gamma0Green N f),
    gamma0Mass_inner_unfold_twoCell_integral N r Y hY (h2SectionLaplacianSeed ψ) hΔψ (gamma0Green N f),
    gamma0Mass_inner_unfold_twoCell_integral N r Y hY ψ hψ f] at he
  apply mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)
  simpa only [mul_add,h2SectionLaplacianSeed_apply] using he

end ArtinMatthews
