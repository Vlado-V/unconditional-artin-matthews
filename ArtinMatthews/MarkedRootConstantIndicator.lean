module

public import ArtinMatthews.MarkedRootGoodPathReplacement
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

/-! Exact complex weighting of the genuine path-indicator comparison.
The physical kernel is constant after coordinates and labels are fixed. -/

noncomputable section
namespace ArtinMatthews
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedRootConstantIndicatorSum {S : ℕ}
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) (U V : ℝ)
    (T : Set (ℝ × (ℝ × ℝ))) (c : ℂ) : ℂ :=
  ∑ p ∈ fixedURootMatrixBoxPoints g₀ U (16*U) 0 1 V (2*V) true true true true true true,
    if markedRootNormalizedPoint U V p ∈ T then c else 0

theorem markedRootConstantIndicatorSum_eq {S : ℕ}
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) (U V : ℝ)
    (T : Set (ℝ × (ℝ × ℝ))) (c : ℂ) :
    markedRootConstantIndicatorSum g₀ U V T c = (markedRootIndicatorCount g₀ U V T:ℝ) • c := by
  unfold markedRootConstantIndicatorSum
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const,markedRootIndicatorCount,Nat.cast_smul_eq_nsmul]

theorem markedRootConstantIndicator_integrable (T : Set (ℝ × (ℝ × ℝ)))
    (hT : MeasurableSet T) (c : ℂ) :
    Integrable (fun p => if p ∈ T then c else 0) markedNormalizedRootMeasure := by
  let : IsFiniteMeasure markedNormalizedRootMeasure := by
    unfold markedNormalizedRootMeasure
    infer_instance
  exact (integrable_const c).indicator hT

theorem markedRootConstantIndicator_integral (T : Set (ℝ × (ℝ × ℝ)))
    (hT : MeasurableSet T) (c : ℂ) :
    (∫ p,(if p ∈ T then c else 0) ∂markedNormalizedRootMeasure) = markedNormalizedRootMeasure.real T • c := by
  exact integral_indicator_const c hT

theorem markedRootConstantIndicator_error {S : ℕ}
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) (U V d : ℝ)
    (T : Set (ℝ × (ℝ × ℝ))) (hT : MeasurableSet T) (c : ℂ) :
    ‖markedRootConstantIndicatorSum g₀ U V T c -
      d • (∫ p,(if p ∈ T then c else 0) ∂markedNormalizedRootMeasure)‖ =
      ‖c‖*|(markedRootIndicatorCount g₀ U V T:ℝ)-d*markedNormalizedRootMeasure.real T| := by
  rw [markedRootConstantIndicatorSum_eq,markedRootConstantIndicator_integral T hT c,
    smul_smul,← sub_smul,norm_smul,Real.norm_eq_abs,mul_comm]

theorem markedRootGoodPath_constant_error {J ι : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) {M : ℕ} (I : Finset ι)
    (a : ι → MarkedRawActive (markedRawActualPrimeBand e x) M) (d₀ Y U V : ℝ)
    (z w : ι → Fin 2 → ℝ) {S : ℕ} (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) (c : ℂ) :
    ‖markedRootConstantIndicatorSum g₀ U V (markedRootGoodPathSet e x I a d₀ Y U V z w) c -
      (U*V/((riemannZeta 2).re*(Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)):ℝ))) •
        (∫ p,(if p ∈ markedRootGoodPathSet e x I a d₀ Y U V z w then c else 0) ∂markedNormalizedRootMeasure)‖ =
      ‖c‖*|(markedRootIndicatorCount g₀ U V (markedRootGoodPathSet e x I a d₀ Y U V z w):ℝ)-
        (U*V/((riemannZeta 2).re*(Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)):ℝ)))*
          markedNormalizedRootMeasure.real (markedRootGoodPathSet e x I a d₀ Y U V z w)| := by
  exact markedRootConstantIndicator_error g₀ U V _ _
    (markedRootGoodPathSet_measurable e x I a d₀ Y U V z w) c

end ArtinMatthews
