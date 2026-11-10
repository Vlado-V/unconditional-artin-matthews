module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
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

/-! Translation and reflection identities for actual Fréchet derivatives. -/

noncomputable section
namespace OAI.Analysis.PDE.Schauder

theorem fderiv_reflect_translate {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (hf : Differentiable ℝ f) (x y : E) :
    fderiv ℝ (fun z => f (x - z)) y = -fderiv ℝ f (x - y) := by
  have hg : HasFDerivAt (fun z : E => x - z) (-ContinuousLinearMap.id ℝ E) y := by
    simpa using! (hasFDerivAt_const x y).sub (hasFDerivAt_id y)
  simpa using! ((hf (x - y)).hasFDerivAt.comp y hg).fderiv

theorem second_fderiv_reflect_translate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ 2 f) (x y v w : E) :
    fderiv ℝ (fderiv ℝ (fun z => f (x - z))) y v w =
      fderiv ℝ (fderiv ℝ f) (x - y) v w := by
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have he : fderiv ℝ (fun z => f (x - z)) = fun z => -fderiv ℝ f (x - z) := by
    funext z
    exact fderiv_reflect_translate f (hf.differentiable (by norm_num)) x z
  rw [he]
  change (fderiv ℝ (-(fun z => fderiv ℝ f (x - z))) y) v w = _
  rw [fderiv_neg, fderiv_reflect_translate (fderiv ℝ f) (hDf.differentiable one_ne_zero) x y, neg_neg]

end OAI.Analysis.PDE.Schauder
