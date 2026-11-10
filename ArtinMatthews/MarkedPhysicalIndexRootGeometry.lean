module

public import ArtinMatthews.MarkedPhysicalCoordinateGoodVolume
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

/-! Genuine bounded complements and the literal good set on every pure
coordinate index, including indices with no valid physical lift. -/

noncomputable section
namespace ArtinMatthews
open MeasureTheory
attribute [local instance] Classical.propDecidable

def markedPhysicalCoordinateIndexGoodSet {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x d₀ Y U V : ℝ) {n R : ℕ}
    (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) n R)
    (hR : 1≤R) : Set (ℝ × (ℝ × ℝ)) :=
  markedRootGoodPathSet e x Finset.univ
    (markedPhysicalCoordinateIndexRawActive (fun j => markedLogPowerBand (e j) x)
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) ⌊(Real.log x)^(1/100:ℝ)⌋₊ i)
    d₀ Y U V
    (fun v => markedRootIntegerVector (markedPhysicalCoordinateIndexPath i.2.1 v))
    (fun v => markedRootIntegerVector (markedPrimitiveCoordinateCompletion
      (markedPhysicalCoordinateIndexPath i.2.1 v) (markedPhysicalCoordinateIndexPath_primitive hR i.2.1 v)))

theorem markedPhysicalCoordinateIndexGoodSet_volume {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x d₀ Y U V : ℝ) {n R : ℕ}
    (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) n R)
    (hR : 1≤R) :
    markedNormalizedRootMeasure.real (markedPhysicalCoordinateIndexGoodSet e x d₀ Y U V i hR) =
      markedPhysicalCoordinateIndexGoodVolume e x d₀ Y U V i hR := rfl

theorem markedPhysicalCoordinateIndexGoodSet_measurable {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x d₀ Y U V : ℝ) {n R : ℕ}
    (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) n R)
    (hR : 1≤R) : MeasurableSet (markedPhysicalCoordinateIndexGoodSet e x d₀ Y U V i hR) :=
  markedRootGoodPathSet_measurable _ _ _ _ _ _ _ _ _ _

theorem markedPhysicalCoordinateIndexPath_real_bound {n R : ℕ} (hR : 1≤R)
    (tail : Fin n → ↥(markedPrimitiveCoordinateTube R)) (v : Fin (n+1)) :
    |((markedPhysicalCoordinateIndexPath tail v).1:ℝ)|≤R ∧
      |((markedPhysicalCoordinateIndexPath tail v).2:ℝ)|≤R := by
  have h := (markedPrimitiveCoordinateTube_mem R _).mp (markedPhysicalCoordinateIndexPath_mem hR tail v)
  exact ⟨by exact_mod_cast h.1,by exact_mod_cast h.2.1⟩

theorem markedPhysicalCoordinateIndexCompletion_bound {n R : ℕ} (hR : 1≤R)
    (tail : Fin n → ↥(markedPrimitiveCoordinateTube R)) (v : Fin (n+1)) :
    |((markedPrimitiveCoordinateCompletion (markedPhysicalCoordinateIndexPath tail v)
      (markedPhysicalCoordinateIndexPath_primitive hR tail v)).1:ℝ)|≤(R:ℝ)+1 ∧
    |((markedPrimitiveCoordinateCompletion (markedPhysicalCoordinateIndexPath tail v)
      (markedPhysicalCoordinateIndexPath_primitive hR tail v)).2:ℝ)|≤(R:ℝ)+1 :=
  markedPrimitiveCoordinateCompletion_real_bound _ _ R
    (markedPhysicalCoordinateIndexPath_real_bound hR tail v).1
    (markedPhysicalCoordinateIndexPath_real_bound hR tail v).2

end ArtinMatthews
