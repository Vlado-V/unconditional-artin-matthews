module

public import ArtinMatthews.SpectralGamma0EllipticTests
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

/-! Native compact tests remain smooth and compact under their literal
positive Euclidean Laplacian, with no enlargement of support. -/
noncomputable section
open Set
open scoped ContDiff
namespace ArtinMatthews

theorem spectralEllipticPositiveLaplacian_smooth (χ : (Fin 2 → ℝ) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) : ContDiff ℝ ∞ (spectralEllipticPositiveLaplacian χ) := by
  apply ContDiff.neg
  apply ContDiff.sum
  intro i _
  have hd : ContDiff ℝ ∞ (fun y => fderiv ℝ χ y (Pi.single i 1)) :=
    (hχ.fderiv_right (by simp)).clm_apply contDiff_const
  exact (hd.fderiv_right (by simp)).clm_apply contDiff_const

theorem spectralEllipticPositiveLaplacian_support (χ : (Fin 2 → ℝ) → ℝ) :
    tsupport (spectralEllipticPositiveLaplacian χ) ⊆ tsupport χ := by
  apply closure_minimal _ (isClosed_tsupport χ)
  intro x hx
  by_contra hn
  have hz : ∀ i : Fin 2, fderiv ℝ (fun y => fderiv ℝ χ y (Pi.single i 1)) x = 0 := by
    intro i
    apply fderiv_of_notMem_tsupport
    exact fun hi => hn (tsupport_fderiv_apply_subset ℝ (Pi.single i 1) hi)
  apply hx
  simp only [spectralEllipticPositiveLaplacian,hz,zero_apply,
    Finset.sum_const_zero,neg_zero]

theorem spectralEllipticPositiveLaplacian_compact (χ : (Fin 2 → ℝ) → ℝ)
    (hc : HasCompactSupport χ) : HasCompactSupport (spectralEllipticPositiveLaplacian χ) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (spectralEllipticPositiveLaplacian_support χ)

end ArtinMatthews
