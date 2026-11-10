module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Green
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Reflection


set_option backward.privateInPublic true
@[expose] public section

/-! Differentiating a scalar convolution on either its compact data or its smooth kernel. -/

noncomputable section
open _root_.MeasureTheory
open scoped Convolution
namespace OAI.Analysis.PDE.Schauder

def scalarConvolution {m : ℕ} (K f : EuclideanSpace ℝ (Fin m) → ℝ)
    (x : EuclideanSpace ℝ (Fin m)) : ℝ := ∫ y, K y * f (x - y)

theorem contDiff_scalarConvolution {m : ℕ} (K f : EuclideanSpace ℝ (Fin m) → ℝ)
    (hK : LocallyIntegrable K) {k : ℕ∞} (hf : ContDiff ℝ k f) (hfc : HasCompactSupport f) :
    ContDiff ℝ k (scalarConvolution K f) :=
  hfc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hK hf

theorem fderiv_scalarConvolution_data {m : ℕ} (K f : EuclideanSpace ℝ (Fin m) → ℝ)
    (hK : LocallyIntegrable K) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (x u : EuclideanSpace ℝ (Fin m)) :
    fderiv ℝ (scalarConvolution K f) x u = ∫ y, K y * fderiv ℝ f (x - y) u := by
  have hi := (hfc.fderiv ℝ).convolutionExists_right
    ((ContinuousLinearMap.mul ℝ ℝ).precompR (EuclideanSpace ℝ (Fin m)))
    hK (hf.continuous_fderiv one_ne_zero) x
  change fderiv ℝ (K ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] f) x u = _
  rw [(hfc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hK hf x).fderiv]
  change (∫ y, (ContinuousLinearMap.mul ℝ ℝ).precompR (EuclideanSpace ℝ (Fin m))
    (K y) (fderiv ℝ f (x - y))) u = _
  rw [ContinuousLinearMap.integral_apply hi]
  rfl

theorem integral_convolution_fderiv_transfer {m : ℕ} (K f : EuclideanSpace ℝ (Fin m) → ℝ)
    (hK : ContDiff ℝ 1 K) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (x u : EuclideanSpace ℝ (Fin m)) :
    (∫ y, K y * fderiv ℝ f (x - y) u) = ∫ y, fderiv ℝ K y u * f (x - y) := by
  have hg : ContDiff ℝ 1 (fun y => f (x - y)) := hf.comp (contDiff_const.sub contDiff_id)
  have hgc : HasCompactSupport (fun y => f (x - y)) := hfc.comp_homeomorph (Homeomorph.subLeft x)
  have h := integral_mul_fderiv_compact K (fun y => f (x - y)) hK hg hgc u
  simp only [fderiv_reflect_translate f (hf.differentiable one_ne_zero),
    neg_apply, mul_neg, integral_neg] at h
  linarith

theorem fderiv_scalarConvolution_kernel {m : ℕ} (K f : EuclideanSpace ℝ (Fin m) → ℝ)
    (hK : ContDiff ℝ 1 K) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (x u : EuclideanSpace ℝ (Fin m)) :
    fderiv ℝ (scalarConvolution K f) x u = ∫ y, fderiv ℝ K y u * f (x - y) := by
  rw [fderiv_scalarConvolution_data K f hK.continuous.locallyIntegrable hf hfc x u,
    integral_convolution_fderiv_transfer K f hK hf hfc x u]

end OAI.Analysis.PDE.Schauder
