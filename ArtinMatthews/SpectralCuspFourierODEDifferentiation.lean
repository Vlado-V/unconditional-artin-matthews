module

public import ArtinMatthews.CuspAverageProjectionBase
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import ArtinMatthews.SpectralCuspHorizontalMeanWeak
public import ArtinMatthews.SpectralCuspProjectedTail
public import ArtinMatthews.SpectralCuspWeakRegularityLocal
public import ArtinMatthews.SpectralCuspWeakRegularityRepresentative
public import ArtinMatthews.SpectralRellichCoordinates
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Actual classical differentiation of horizontal compact-cell integrals.
The genuine compact-test integration-by-parts identity and the proved local
weak-derivative regularity theorem justify differentiation. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff

namespace ArtinMatthews

theorem cuspHorizontalMean_hasDerivAt {F : ℝ × ℝ → ℂ}
    (hF : ContDiff ℝ ∞ F) (w : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (cuspHorizontalMean w F)
      (cuspHorizontalMean w (fun p => fderiv ℝ F p (0, 1)) y) y := by
  have hc := cuspHorizontalMean_continuous hF.continuous w
  have hd : Continuous (fun p => fderiv ℝ F p (0, 1)) :=
    (hF.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdc := cuspHorizontalMean_continuous hd w
  have hw : SpectralCuspWeakRegularity.PositiveWeakDerivative
      (cuspHorizontalMean w F) (cuspHorizontalMean w (fun p => fderiv ℝ F p (0, 1))) := by
    intro ρ hρ hρc hρs
    rw [SpectralCuspWeakRegularity.positive_test_setIntegral_eq _ (tsupport_deriv_subset.trans hρs),
      SpectralCuspWeakRegularity.positive_test_setIntegral_eq _ hρs]
    exact cuspHorizontalMean_weak_verticalDerivative hF w ρ hρ hρc
  exact SpectralCuspWeakRegularity.positiveWeakDerivative_hasDerivAt
    (hc.continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (hdc.continuousOn.locallyIntegrableOn measurableSet_Ioi) hw
    hc.continuousOn hdc.continuousOn EventuallyEq.rfl EventuallyEq.rfl y hy

def cuspHorizontalWeightedMean (w : ℝ) (χ : ℝ → ℂ) (F : ℝ × ℝ → ℂ) : ℝ → ℂ :=
  cuspHorizontalMean w (fun p => χ p.1 * F p)

theorem cuspHorizontalWeightedMean_continuous (w : ℝ) {χ : ℝ → ℂ}
    (hχ : Continuous χ) {F : ℝ × ℝ → ℂ} (hF : Continuous F) :
    Continuous (cuspHorizontalWeightedMean w χ F) :=
  cuspHorizontalMean_continuous ((hχ.comp continuous_fst).mul hF) w

theorem spectralPlane_vertical_product (χ : ℝ → ℂ) (F : ℝ × ℝ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hF : ContDiff ℝ ∞ F) (p : ℝ × ℝ) :
    fderiv ℝ (fun q : ℝ × ℝ => χ q.1 * F q) p (0, 1) =
      χ p.1 * fderiv ℝ F p (0, 1) := by
  have hprod : DifferentiableAt ℝ (fun q : ℝ × ℝ => χ q.1 * F q) p :=
    (((hχ.differentiable (by simp)) p.1).comp p differentiableAt_fst).mul
      ((hF.differentiable (by simp)) p)
  rw [← spectralPlanePartialY_eq_fderiv hprod]
  unfold spectralPlanePartialY
  change deriv (fun t : ℝ => χ p.1 * F (p.1, t)) p.2 = χ p.1 * fderiv ℝ F p (0, 1)
  rw [deriv_const_mul]
  · rw [← spectralPlanePartialY_eq_fderiv ((hF.differentiable (by simp)) p)]
    rfl
  · exact ((hF.differentiable (by simp)) p).comp p.2
      ((differentiableAt_const p.1).prodMk differentiableAt_id)

theorem cuspHorizontalWeightedMean_hasDerivAt (w : ℝ) {χ : ℝ → ℂ}
    (hχ : ContDiff ℝ ∞ χ) {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (cuspHorizontalWeightedMean w χ F)
      (cuspHorizontalWeightedMean w χ (fun p => fderiv ℝ F p (0, 1)) y) y := by
  have hg : ContDiff ℝ ∞ (fun p : ℝ × ℝ => χ p.1 * F p) :=
    (hχ.comp contDiff_fst).mul hF
  have he : (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => χ q.1 * F q) p (0, 1)) =
      (fun p => χ p.1 * fderiv ℝ F p (0, 1)) :=
    funext (spectralPlane_vertical_product χ F hχ hF)
  simpa only [cuspHorizontalWeightedMean, he] using cuspHorizontalMean_hasDerivAt hg w hy

theorem cuspHorizontalWeightedMean_deriv (w : ℝ) {χ : ℝ → ℂ}
    (hχ : ContDiff ℝ ∞ χ) {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    {y : ℝ} (hy : 0 < y) :
    deriv (cuspHorizontalWeightedMean w χ F) y =
      cuspHorizontalWeightedMean w χ (fun p => fderiv ℝ F p (0, 1)) y :=
  (cuspHorizontalWeightedMean_hasDerivAt w hχ hF hy).deriv

end ArtinMatthews
