module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.Normed.Function.Holder.C2HolderBanach
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
public import OAI.Analysis.Normed.Function.Holder.Banach.Construct
public import OAI.Analysis.Normed.Function.Holder.C2HolderRegularity


set_option backward.privateInPublic true
@[expose] public section

open Set Filter
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.Normed.Function.Holder.C2Holder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω K : Set E} {hΩK : Ω ⊆ K} {α : ℝ}

local instance extFirstDerivativeNormedGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance extFirstDerivativeNormedSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance extSecondDerivativeNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) :=
  inferInstance
local instance extSecondDerivativeNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) :=
  inferInstance

/-- If the interior is dense in the underlying closed domain, the jet is
uniquely determined by the function. There are no independent boundary jets. -/
theorem value_injective (hKΩ : K ⊆ closure Ω) :
    Function.Injective (C2Holder.value (F := F) (hΩK := hΩK) (α := α)) := by
  intro f g hfg
  have hG : EqOn (boundedZeroExtension (C2Holder.firstDerivative f))
      (boundedZeroExtension (C2Holder.firstDerivative g)) Ω := by
    intro x hx
    rw [← (C2Holder.hasFDerivAt_value_extension f hx).fderiv,
      ← (C2Holder.hasFDerivAt_value_extension g hx).fderiv, hfg]
  have hGK := hG.of_subset_closure
    (continuousOn_boundedZeroExtension (C2Holder.firstDerivative f))
    (continuousOn_boundedZeroExtension (C2Holder.firstDerivative g)) hΩK hKΩ
  have hGval : C2Holder.firstDerivative f = C2Holder.firstDerivative g := by
    apply BoundedContinuousFunction.ext
    intro x
    simpa only [boundedZeroExtension_apply _ x.property] using hGK x.property
  have hH : EqOn (boundedZeroExtension (F := E →L[ℝ] E →L[ℝ] F) (C2Holder.secondDerivative f))
      (boundedZeroExtension (F := E →L[ℝ] E →L[ℝ] F) (C2Holder.secondDerivative g)) Ω := by
    intro x hx
    rw [← (C2Holder.hasFDerivAt_first_extension f hx).fderiv,
      ← (C2Holder.hasFDerivAt_first_extension g hx).fderiv, hGval]
  have hHK := hH.of_subset_closure
    (continuousOn_boundedZeroExtension (F := E →L[ℝ] E →L[ℝ] F) (C2Holder.secondDerivative f))
    (continuousOn_boundedZeroExtension (F := E →L[ℝ] E →L[ℝ] F) (C2Holder.secondDerivative g)) hΩK hKΩ
  have hHval : C2Holder.secondDerivative f = C2Holder.secondDerivative g := by
    apply BoundedContinuousFunction.ext
    intro x
    simpa only [boundedZeroExtension_apply _ x.property] using hHK x.property
  apply Subtype.ext
  apply Prod.ext hfg
  apply Prod.ext hGval
  exact OAI.Analysis.Normed.Function.Holder.HolderMap.value_injective hHval

end OAI.Analysis.Normed.Function.Holder.C2Holder
