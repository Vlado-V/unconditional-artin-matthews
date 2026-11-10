module

public import ArtinMatthews.MarkedPhysicalCoordinateIndexActivePath
public import ArtinMatthews.MarkedRootGoodPathReplacement
public import ArtinMatthews.MarkedPrimitiveCoordinateCompletion
public import ArtinMatthews.MarkedRawGoodRootTransport
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual normalized good-path volume on the fixed coordinate
carrier. The finite measure has total mass 15, kept explicitly. -/
namespace ArtinMatthews
open MeasureTheory
open scoped BigOperators Classical
noncomputable section

theorem markedNormalizedRootMeasure_univ : markedNormalizedRootMeasure Set.univ=15 := by
  unfold markedNormalizedRootMeasure
  rw [← Set.univ_prod_univ,Measure.prod_prod,← Set.univ_prod_univ,Measure.prod_prod]
  simp only [Measure.restrict_apply_univ,Real.volume_Icc]
  norm_num

theorem markedNormalizedRootMeasure_real_le (T : Set (ℝ × (ℝ × ℝ))) :
    0 ≤ markedNormalizedRootMeasure.real T ∧ markedNormalizedRootMeasure.real T≤15 := by
  refine ⟨ENNReal.toReal_nonneg,?_⟩
  have h := ENNReal.toReal_mono (by rw [markedNormalizedRootMeasure_univ]; norm_num)
    (measure_mono (Set.subset_univ T) : markedNormalizedRootMeasure T ≤ markedNormalizedRootMeasure Set.univ)
  simpa only [Measure.real,markedNormalizedRootMeasure_univ,ENNReal.toReal_ofNat] using h

theorem markedPhysicalCoordinateIndexPath_primitive {n B : ℕ} (hB : 1≤B)
    (tail : Fin n → ↥(markedPrimitiveCoordinateTube B)) (v : Fin (n+1)) :
    IsCoprime (markedPhysicalCoordinateIndexPath tail v).1 (markedPhysicalCoordinateIndexPath tail v).2 :=
  ((markedPrimitiveCoordinateTube_mem B _).mp (markedPhysicalCoordinateIndexPath_mem hB tail v)).2.2

def markedPhysicalCoordinateIndexGoodVolume {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x d₀ Y U V : ℝ) {n B : ℕ}
    (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) n B)
    (hB : 1≤B) : ℝ :=
  markedNormalizedRootMeasure.real
    (markedRootGoodPathSet e x Finset.univ
      (markedPhysicalCoordinateIndexRawActive (fun j => markedLogPowerBand (e j) x)
        (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) ⌊(Real.log x)^(1/100:ℝ)⌋₊ i)
      d₀ Y U V
      (fun v => markedRootIntegerVector (markedPhysicalCoordinateIndexPath i.2.1 v))
      (fun v => markedRootIntegerVector (markedPrimitiveCoordinateCompletion
        (markedPhysicalCoordinateIndexPath i.2.1 v) (markedPhysicalCoordinateIndexPath_primitive hB i.2.1 v))))

theorem markedPhysicalCoordinateIndexGoodVolume_bounds {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x d₀ Y U V : ℝ) {n B : ℕ}
    (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) n B)
    (hB : 1≤B) :
    0 ≤ markedPhysicalCoordinateIndexGoodVolume e x d₀ Y U V i hB ∧
      markedPhysicalCoordinateIndexGoodVolume e x d₀ Y U V i hB≤15 :=
  markedNormalizedRootMeasure_real_le _

end
end ArtinMatthews
