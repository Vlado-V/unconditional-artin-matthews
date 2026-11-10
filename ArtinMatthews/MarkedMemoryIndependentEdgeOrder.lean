module

public import ArtinMatthews.MarkedMemoryHistoryEdgeVertices
public import ArtinMatthews.MarkedMemoryIndependentHistory
public import ArtinMatthews.MarkedMemoryCopiedSlotGeometry
public import ArtinMatthews.MarkedMemoryIndependentEdgeProduct
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

/-! The genuine position-only physical edge kernel is independent of
common-survivor slot order. This is proved from the actual joint kernel
and the fixed outgoing/incoming identity slots. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)

theorem markedMemoryIndependentRawEdge_position_order (F : Z → ℂ)
    (v : ℕ) (hv : v < n) (left right : J → Equiv.Perm (Fin pads)) :
    markedMemoryRawEdgeValue hZ ψ η d₀ Y Q (fun s => F s.1) (markedMemoryIndependentEdge hZ d v hv left) =
      markedMemoryRawEdgeValue hZ ψ η d₀ Y Q (fun s => F s.1) (markedMemoryIndependentEdge hZ d v hv right) := by
  rw [markedMemoryIndependentRawEdge_joint,markedMemoryIndependentRawEdge_joint]
  apply markedRawEdgeJointCoefficient_slots_positionMemory hZ ψ η d₀ Y Q 1 (fun z _ => F z)
  · intro j
    change markedMemorySlotFamilySource _ _ _ _ (markedMemoryIndependentSlotPairs hZ d v hv left) j (Fin.last pads) =
      markedMemorySlotFamilySource _ _ _ _ (markedMemoryIndependentSlotPairs hZ d v hv right) j (Fin.last pads)
    rw [markedMemorySlotFamilySource_last,markedMemorySlotFamilySource_last]
  · intro j
    change markedMemorySlotFamilyTargetInverse _ _ _ _ (markedMemoryIndependentSlotPairs hZ d v hv left) j (Fin.last pads) =
      markedMemorySlotFamilyTargetInverse _ _ _ _ (markedMemoryIndependentSlotPairs hZ d v hv right) j (Fin.last pads)
    rw [markedMemorySlotFamilyTargetInverse_last,markedMemorySlotFamilyTargetInverse_last]

theorem markedMemoryIndependentRawProduct_position_order (F : ℕ → Z → ℂ)
    (left right : Fin n → J → Equiv.Perm (Fin pads)) (offset : ℕ) :
    markedMemoryHistoryRawEdgeProduct hZ ψ η d₀ Y Q (fun t s => F t s.1) n offset
      (markedMemoryIndependentHistory hZ d left) =
    markedMemoryHistoryRawEdgeProduct hZ ψ η d₀ Y Q (fun t s => F t s.1) n offset
      (markedMemoryIndependentHistory hZ d right) := by
  rw [markedMemoryIndependent_rawEdgeProduct,markedMemoryIndependent_rawEdgeProduct]
  exact Finset.prod_congr rfl (fun v _ =>
    markedMemoryIndependentRawEdge_position_order hZ d ψ η d₀ Y Q (F (offset+v.val)) v.val v.2 _ _)

end
end ArtinMatthews
