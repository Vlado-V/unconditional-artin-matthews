module

public import ArtinMatthews.SourceArchProjectiveUpperAction
public import ArtinMatthews.SourceArchPGLSurjectivity
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! Hyperbolic volume in the actual complex Gram chart is invariant under the full projective group. -/
namespace ArtinMatthews.SourceArchJacquet
open Matrix OAI.CubicEisenstein MeasureTheory
open scoped MatrixGroups
noncomputable section

def sourceArchHyperbolicMeasure : Measure SourceArchUpperHalfSpace :=
  Measure.map sourceArchHyperbolicHomeomorph.symm hyperbolicVolume

lemma sourceArchHyperbolicMeasure_specialLinear (a : SL(2, ℂ)) :
    Measure.map (sourceArchGLUpperAction (a : GL (Fin 2) ℂ)) sourceArchHyperbolicMeasure =
      sourceArchHyperbolicMeasure := by
  rw [sourceArchHyperbolicMeasure, Measure.map_map
    (sourceArchGLUpperAction_continuous _).measurable sourceArchHyperbolicHomeomorph.symm.measurable]
  have he : sourceArchGLUpperAction (a : GL (Fin 2) ℂ) ∘ sourceArchHyperbolicHomeomorph.symm =
      sourceArchHyperbolicHomeomorph.symm ∘ (fun w : HyperbolicSpace => a • w) := by
    funext w
    simp only [Function.comp_apply, sourceArchGLUpperAction_specialLinear, Homeomorph.apply_symm_apply]
  rw [he, ← Measure.map_map sourceArchHyperbolicHomeomorph.symm.measurable
    (continuous_hyperbolic_action a).measurable, hyperbolicVolume_invariant]

lemma sourceArchHyperbolicMeasure_projective (a : PGL(2, ℂ)) :
    Measure.map (sourceArchProjectiveUpperAction a) sourceArchHyperbolicMeasure =
      sourceArchHyperbolicMeasure := by
  obtain ⟨m, rfl⟩ := sourceArchSpecialLinear_toPGL_surjective a
  exact sourceArchHyperbolicMeasure_specialLinear m

lemma sourceArchHyperbolicMeasure_preserving (a : PGL(2, ℂ)) :
    MeasurePreserving (sourceArchProjectiveUpperAction a)
      sourceArchHyperbolicMeasure sourceArchHyperbolicMeasure :=
  ⟨(sourceArchProjectiveUpperAction_continuous a).measurable,
    sourceArchHyperbolicMeasure_projective a⟩

end
end ArtinMatthews.SourceArchJacquet
