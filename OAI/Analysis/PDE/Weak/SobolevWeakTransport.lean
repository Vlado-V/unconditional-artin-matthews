module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Weak.Elliptic.Derivative
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

open Set _root_.MeasureTheory Filter InnerProductSpace
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Weak

variable {X Y V : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Weak derivatives commute with a measure-preserving linear change of
coordinates, including a change between the finite Pi and Euclidean norms. -/
theorem HasWeakDirectionalDerivative.comp_measurePreserving_equiv
    {μ : Measure X} {ν : Measure Y} (e : X ≃L[ℝ] Y)
    (he : MeasurePreserving e μ ν) {v : X} {u g : Y → V}
    (h : HasWeakDirectionalDerivative ν (e v) u g) :
    HasWeakDirectionalDerivative μ v (u ∘ e) (g ∘ e) := by
  intro φ hφ hφs
  let ψ : Y → V := φ ∘ e.symm
  have hψ : ContDiff ℝ 1 ψ := hφ.comp e.symm.contDiff
  have hψs : HasCompactSupport ψ := hφs.comp_homeomorph e.symm.toHomeomorph
  have hd (y : Y) : fderiv ℝ ψ y (e v) = fderiv ℝ φ (e.symm y) v := by
    have hder := ((hφ.differentiable (by norm_num)).differentiableAt.hasFDerivAt).comp y
      e.symm.toContinuousLinearMap.hasFDerivAt
    have hder' : HasFDerivAt ψ
        ((fderiv ℝ φ (e.symm y)).comp e.symm.toContinuousLinearMap) y := hder
    rw [hder'.fderiv]
    simp
  have htest := h ψ hψ hψs
  have hleft := he.integral_comp e.toHomeomorph.measurableEmbedding
    (fun y ↦ inner ℝ (g y) (ψ y))
  have hright := he.integral_comp e.toHomeomorph.measurableEmbedding
    (fun y ↦ inner ℝ (u y) (fderiv ℝ ψ y (e v)))
  rw [← hleft, ← hright] at htest
  simpa only [hd, ψ, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply] using htest

end OAI.Analysis.PDE.Weak
