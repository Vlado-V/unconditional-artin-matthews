module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Convolution
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Positive mollification preserves the Hölder constant, with a quantitative approximation error. -/

noncomputable section
open _root_.MeasureTheory Set Metric
open scoped Convolution
namespace OAI.Analysis.PDE.Schauder

def smoothData {m : ℕ} (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin m) → ℝ) : EuclideanSpace ℝ (Fin m) → ℝ :=
  scalarConvolution (φ.normed volume) f

theorem contDiff_smoothData {m : ℕ} (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : Continuous f) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothData φ f) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℝ)
    φ.contDiff_normed hf.locallyIntegrable

theorem hasCompactSupport_smoothData {m : ℕ} (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hfc : HasCompactSupport f) :
    HasCompactSupport (smoothData φ f) :=
  φ.hasCompactSupport_normed.convolution (ContinuousLinearMap.mul ℝ ℝ) hfc

theorem smoothData_holder {m : ℕ} (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : Continuous f) {H α : ℝ}
    (hh : ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) (x z : EuclideanSpace ℝ (Fin m)) :
    |smoothData φ f x - smoothData φ f z| ≤ H * ‖x - z‖ ^ α := by
  have hi (a : EuclideanSpace ℝ (Fin m)) : Integrable (fun y => φ.normed volume y * f (a - y)) :=
    φ.hasCompactSupport_normed.convolutionExists_left (ContinuousLinearMap.mul ℝ ℝ)
      φ.continuous_normed hf.locallyIntegrable a
  change |(∫ y, φ.normed volume y * f (x - y)) - (∫ y, φ.normed volume y * f (z - y))| ≤ _
  rw [← integral_sub (hi x) (hi z), ← Real.norm_eq_abs]
  have hbound : ∀ᵐ y, ‖φ.normed volume y * f (x - y) - φ.normed volume y * f (z - y)‖ ≤
      φ.normed volume y * (H * ‖x - z‖ ^ α) := by
    filter_upwards with y
    rw [← mul_sub, norm_mul, Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed y), Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed y)
    have he : x - y - (z - y) = x - z := by abel
    simpa only [he] using hh (x - y) (z - y)
  have hb := norm_integral_le_of_norm_le (φ.integrable_normed.mul_const (H * ‖x - z‖ ^ α)) hbound
  simpa only [integral_mul_const, φ.integral_normed, one_mul] using hb

theorem smoothData_error {m : ℕ} (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : Continuous f) {H α : ℝ}
    (hH : 0 ≤ H) (hα : 0 ≤ α)
    (hh : ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) (x : EuclideanSpace ℝ (Fin m)) :
    |smoothData φ f x - f x| ≤ H * φ.rOut ^ α := by
  have h := φ.dist_normed_convolution_le (μ := volume) hf.aestronglyMeasurable
    (x₀ := x) (ε := H * φ.rOut ^ α) (fun y hy => ?_)
  · simpa only [smoothData, scalarConvolution, convolution_def, ContinuousLinearMap.lsmul_apply,
      smul_eq_mul, dist_eq_norm, Real.norm_eq_abs] using h
  · rw [dist_eq_norm, Real.norm_eq_abs]
    exact (hh y x).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) (by simpa only [mem_ball, dist_eq_norm] using hy.le) hα) hH)

end OAI.Analysis.PDE.Schauder
