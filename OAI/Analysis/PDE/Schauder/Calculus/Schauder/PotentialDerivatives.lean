module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Potential
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Order.CompletePartialOrder
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

/-! Differentiation of the Newtonian convolution on the compact smooth data. -/

noncomputable section
open _root_.MeasureTheory
open scoped Convolution
namespace OAI.Analysis.PDE.Schauder

theorem fderiv_newtonianPotential_apply {m : ℕ} (hm : 1 ≤ m)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (x v : EuclideanSpace ℝ (Fin m)) :
    fderiv ℝ (newtonianPotential f) x v = newtonianPotential (fun y => fderiv ℝ f y v) x := by
  have hi := (hfc.fderiv ℝ).convolutionExists_right
    ((ContinuousLinearMap.mul ℝ ℝ).precompR (EuclideanSpace ℝ (Fin m)))
    (locallyIntegrable_newtonianKernel hm) (hf.continuous_fderiv one_ne_zero) x
  rw [(hasFDerivAt_newtonianPotential hm f hf hfc x).fderiv]
  change (∫ y, (ContinuousLinearMap.mul ℝ ℝ).precompR (EuclideanSpace ℝ (Fin m))
    (newtonianKernel m y) (fderiv ℝ f (x - y))) v = _
  rw [ContinuousLinearMap.integral_apply hi]
  rfl

theorem fderiv_apply_const {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : E → E →L[ℝ] F) (x v w : E) (hg : DifferentiableAt ℝ g x) :
    fderiv ℝ (fun y => g y v) x w = fderiv ℝ g x w v := by
  rw [fderiv_clm_apply hg (differentiableAt_const v)]
  simp

theorem second_fderiv_newtonianPotential_apply {m : ℕ} (hm : 1 ≤ m)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (x v w : EuclideanSpace ℝ (Fin m)) :
    fderiv ℝ (fderiv ℝ (newtonianPotential f)) x v w =
      newtonianPotential (fun y => fderiv ℝ (fderiv ℝ f) y v w) x := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hg : ContDiff ℝ 1 (fun y => fderiv ℝ f y w) := hDf.clm_apply contDiff_const
  have hU : ContDiff ℝ 2 (newtonianPotential f) := contDiff_newtonianPotential hm f hf hfc
  have hDU : ContDiff ℝ 1 (fderiv ℝ (newtonianPotential f)) := hU.fderiv_right (by norm_num)
  have he : (fun y => fderiv ℝ (newtonianPotential f) y w) =
      newtonianPotential (fun y => fderiv ℝ f y w) :=
    funext (fun y => fderiv_newtonianPotential_apply hm f hf1 hfc y w)
  rw [← fderiv_apply_const _ x w v (hDU.differentiable one_ne_zero x), he,
    fderiv_newtonianPotential_apply hm _ hg (hfc.fderiv_apply ℝ w)]
  congr 1
  funext y
  exact fderiv_apply_const _ y w v (hDf.differentiable one_ne_zero y)

end OAI.Analysis.PDE.Schauder
