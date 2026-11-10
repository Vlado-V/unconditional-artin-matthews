module

public import ArtinMatthews.MarkedMemoryIndependentEdge
public import ArtinMatthews.MarkedMemoryEdgeOriginLabels
public import ArtinMatthews.MarkedMemoryEdgeQueueLabels
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

/-! The actual reconstructed edge's identity tuple agrees with the
independent target active slots and ordered pending queue. Both facts
are derived from the copied-slot fiber and the explicit queue update. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j, DecidableEq (A j)] [∀ j, Fintype (A j)]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {n : ℕ}
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (v : ℕ) (hv : v < n) (order : J → Equiv.Perm (Fin pads))

def markedMemoryIndependentRawGroupLabel (j : J) :
    (Fin (pads+1) ⊕ Fin ((markedRawEdgeTargetMemory hZ
      (markedRawSlotEquiv (markedMemoryIndependentSourceSlots hZ d v hv order)
        (markedMemoryIndependentPostGhost hZ d v (Nat.le_of_lt hv)))
      (markedMemoryIndependentRawEdge hZ d v hv order)).1.1 j : ℕ)) → A j :=
  markedMemoryEdgeTargetGroupLabel hZ _ (markedMemoryIndependentRawEdge hZ d v hv order)
    (fun j k => d.activeId v j (markedMemoryIndependentSourceSlots hZ d v hv order j k))
    (fun j => (markedMemoryIndependentQueue hZ d (2*v+1) j).get)
    (fun j => (d.lifespan j).incoming (2*v+1)) j

theorem markedMemoryIndependentRawGroupLabel_active (j : J) (k : Fin (pads+1)) :
    markedMemoryIndependentRawGroupLabel hZ d v hv order j (Sum.inl k) =
      d.activeId (v+1) j ((markedMemoryIndependentTargetSlots hZ d v hv order j).symm k) := by
  refine (markedMemoryEdgeTargetGroupLabel_active hZ
    (markedRawSlotEquiv (markedMemoryIndependentSourceSlots hZ d v hv order)
      (markedMemoryIndependentPostGhost hZ d v (Nat.le_of_lt hv)))
    (markedMemoryIndependentRawEdge hZ d v hv order)
    (fun j k => d.activeId v j (markedMemoryIndependentSourceSlots hZ d v hv order j k))
    (fun j => (markedMemoryIndependentQueue hZ d (2*v+1) j).get)
    (fun j => (d.lifespan j).incoming (2*v+1)) j k).trans ?_
  refine Fin.lastCases ?_ (fun k => ?_) k
  · rw [Fin.lastCases_last]
    change (d.lifespan j).incoming (2*v+1) = d.activeId (v+1) j
      (markedMemorySlotFamilyTargetInverse _ _ _ _ (markedMemoryIndependentSlotPairs hZ d v hv order) j (Fin.last pads))
    rw [markedMemorySlotFamilyTargetInverse_last, markedMemoryIndependentIncoming_eq]
  · rw [Fin.lastCases_castSucc]
    exact (markedMemoryIndependentSlotPairs hZ d v hv order j).2.2.2 k

theorem markedMemoryIndependentRawGroupLabel_pending (j : J) :
    List.ofFn (fun k => markedMemoryIndependentRawGroupLabel hZ d v hv order j (Sum.inr k)) =
      markedMemoryIndependentQueue hZ d (2*(v+1)) j := by
  have hout : ∀ j, d.activeId v j (markedMemoryIndependentSourceSlots hZ d v hv order j (Fin.last pads)) =
      (d.lifespan j).outgoing (2*v+1) := by
    intro j
    change d.activeId v j (markedMemorySlotFamilySource _ _ _ _
      (markedMemoryIndependentSlotPairs hZ d v hv order) j (Fin.last pads)) = _
    rw [markedMemorySlotFamilySource_last, markedMemoryIndependentOutgoing_eq]
  exact (markedMemoryEdgeQueueLabel_pending_list hZ (d.position v) (d.position (v+1))
    (markedMemoryIndependentSlottedActive hZ d v hv order)
    (fun j k => d.activeId v j (markedMemoryIndependentSourceSlots hZ d v hv order j k))
    (markedMemoryIndependentQueue hZ d (2*v+1)) (markedMemoryIndependentQueue_nodup hZ d (2*v+1) (by omega))
    (fun j => (d.lifespan j).incoming (2*v+1)) (fun j => (d.lifespan j).outgoing (2*v+1))
    (fun j => decide (2*v+1 < (d.lifespan j).last ((d.lifespan j).outgoing (2*v+1)))) d.particle
    (markedMemoryIndependentQueue_bound hZ d (2*v+1) (by omega))
    (markedMemoryIndependentPromotion_hits hZ d v hv) (markedMemoryIndependentEdge_bound hZ d v hv) hout j).trans
    (congrFun (markedMemoryIndependentQueue_edge hZ d v hv) j)

theorem markedMemoryIndependentRawEdge_target :
    markedRawEdgeTargetState hZ
      (markedRawSlotEquiv (markedMemoryIndependentSourceSlots hZ d v hv order)
        (markedMemoryIndependentPostGhost hZ d v (Nat.le_of_lt hv)))
      (markedMemoryIndependentRawEdge hZ d v hv order) =
        markedRawSlotEquiv (fun j => (markedMemoryIndependentTargetSlots hZ d v hv order j).symm)
          (markedMemoryIndependentState hZ d (v+1) hv) :=
  markedMemoryIdentity_slotChoice_target (fun j a => (d.particle j a).1)
    (d.activeId v) (d.activeId (v+1)) (markedMemoryIndependentOutgoing hZ d v hv)
    (markedMemoryIndependentIncoming hZ d v hv) hZ (d.position v) (d.position (v+1))
    (markedMemoryIndependentMemory hZ d (2*v+1) (by omega))
    (markedMemoryIndependentMemory hZ d (2*(v+1)) (by omega))
    (markedMemoryIndependentSlotPairs hZ d v hv order) (markedMemoryIndependentRawEdge hZ d v hv order)
    rfl (markedMemoryIndependentRawEdge_memory hZ d v hv order)
    (markedMemoryIndependentRawEdge_last hZ d v hv order)

end
end ArtinMatthews
