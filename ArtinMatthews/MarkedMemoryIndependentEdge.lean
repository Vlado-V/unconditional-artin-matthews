module

public import ArtinMatthews.MarkedMemoryIndependentActive
public import ArtinMatthews.MarkedMemoryHistoryEdgeChoice
public import ArtinMatthews.MarkedMemoryLifespanEdgeQueueTarget
public import ArtinMatthews.MarkedMemoryQueueState
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

/-! Construct the actual slotted edge from independent lifespan data.
The outgoing/incoming indices and the copied-slot matching were derived
from active incidences. The old-only promotion, fresh label and store
are derived from the pending identity queue and endpoint rules. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j, DecidableEq (A j)] [∀ j, Fintype (A j)]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {n : ℕ}
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)

def markedMemoryIndependentSourceSlots (v : ℕ) (hv : v < n) (order : J → Equiv.Perm (Fin pads)) :=
  markedMemorySlotFamilySource _ _ _ _ (markedMemoryIndependentSlotPairs hZ d v hv order)

def markedMemoryIndependentTargetSlots (v : ℕ) (hv : v < n) (order : J → Equiv.Perm (Fin pads)) :=
  fun j => (markedMemoryIndependentSlotPairs hZ d v hv order j).1.2

def markedMemoryIndependentSlottedActive (v : ℕ) (hv : v < n) (order : J → Equiv.Perm (Fin pads)) :
    MarkedRawActive P (pads+1) :=
  fun j k => (d.particle j (d.activeId v j (markedMemoryIndependentSourceSlots hZ d v hv order j k))).1

theorem markedMemoryIndependentPromotion_hits (v : ℕ) (hv : v < n) :
    ∀ j k, (markedMemoryIndependentQueue hZ d (2*v+1) j).get k = (d.lifespan j).incoming (2*v+1) →
      MarkedRawParticleHits (P j) (d.position (v+1)).1 (hZ _ (d.position (v+1)).2)
        (d.particle j ((markedMemoryIndependentQueue hZ d (2*v+1) j).get k)) := by
  intro j k he
  have hm := (markedMemoryPendingQueueAt_mem (d.lifespan j) (2*v+1) (by omega) _).mp (List.get_mem _ k)
  rw [he] at hm ⊢
  exact d.promotion_hit v hv j hm.1 hm.2.1 hm.2.2

theorem markedMemoryIndependentEdge_bound (v : ℕ) (hv : v < n) :
    (∑ j, (markedMemoryEdgeQueueAfter (markedMemoryIndependentQueue hZ d (2*v+1))
      (markedMemoryIndependentQueue_nodup hZ d (2*v+1) (by omega))
      (fun j => (d.lifespan j).incoming (2*v+1)) (fun j => (d.lifespan j).outgoing (2*v+1))
      (fun j => decide (2*v+1 < (d.lifespan j).last ((d.lifespan j).outgoing (2*v+1)))) j).length) ≤ B := by
  rw [markedMemoryIndependentQueue_edge hZ d v hv]
  exact markedMemoryIndependentQueue_bound hZ d (2*(v+1)) (by omega)

def markedMemoryIndependentRawEdge (v : ℕ) (hv : v < n) (order : J → Equiv.Perm (Fin pads)) :
    MarkedRawEdgeChoice hZ (markedRawSlotEquiv (markedMemoryIndependentSourceSlots hZ d v hv order)
      (markedMemoryIndependentPostGhost hZ d v (Nat.le_of_lt hv))) :=
  markedMemoryEdgeQueueChoice hZ (d.position v) (d.position (v+1))
    (markedMemoryIndependentSlottedActive hZ d v hv order)
    (markedMemoryIndependentQueue hZ d (2*v+1))
    (markedMemoryIndependentQueue_nodup hZ d (2*v+1) (by omega))
    (fun j => (d.lifespan j).incoming (2*v+1)) (fun j => (d.lifespan j).outgoing (2*v+1))
    (fun j => decide (2*v+1 < (d.lifespan j).last ((d.lifespan j).outgoing (2*v+1))))
    d.particle (markedMemoryIndependentQueue_bound hZ d (2*v+1) (by omega))
    (markedMemoryIndependentPromotion_hits hZ d v hv) (markedMemoryIndependentEdge_bound hZ d v hv)

theorem markedMemoryIndependentSource_last (v : ℕ) (hv : v < n) (order : J → Equiv.Perm (Fin pads)) (j : J) :
    ((markedRawActiveSplit pads)
      (markedRawSlotEquiv (markedMemoryIndependentSourceSlots hZ d v hv order)
        (markedMemoryIndependentPostGhost hZ d v (Nat.le_of_lt hv))).2.1).2 j =
      (d.particle j ((d.lifespan j).outgoing (2*v+1))).1 := by
  change (d.particle j (d.activeId v j
    (markedMemorySlotFamilySource _ _ _ _ (markedMemoryIndependentSlotPairs hZ d v hv order) j (Fin.last pads)))).1 = _
  rw [markedMemorySlotFamilySource_last, markedMemoryIndependentOutgoing_eq]

theorem markedMemoryIndependentRawEdge_memory (v : ℕ) (hv : v < n) (order : J → Equiv.Perm (Fin pads)) :
    markedRawEdgeTargetMemory hZ
      (markedRawSlotEquiv (markedMemoryIndependentSourceSlots hZ d v hv order)
        (markedMemoryIndependentPostGhost hZ d v (Nat.le_of_lt hv)))
      (markedMemoryIndependentRawEdge hZ d v hv order) =
        markedMemoryIndependentMemory hZ d (2*(v+1)) (by omega) := by
  refine (markedMemoryEdgeQueueChoice_target_memory hZ (d.position v) (d.position (v+1))
    (markedMemoryIndependentSlottedActive hZ d v hv order)
    (markedMemoryIndependentQueue hZ d (2*v+1))
    (markedMemoryIndependentQueue_nodup hZ d (2*v+1) (by omega))
    (fun j => (d.lifespan j).incoming (2*v+1)) (fun j => (d.lifespan j).outgoing (2*v+1))
    (fun j => decide (2*v+1 < (d.lifespan j).last ((d.lifespan j).outgoing (2*v+1)))) d.particle
    (markedMemoryIndependentQueue_bound hZ d (2*v+1) (by omega))
    (markedMemoryIndependentPromotion_hits hZ d v hv) (markedMemoryIndependentEdge_bound hZ d v hv) ?_).trans ?_
  · intro j hj
    exact (d.store_anchor v hv j (of_decide_eq_true hj)).trans
      (congrArg (fun p => markedRawAnchoredParticle (P j) p (d.position v).1 (hZ _ (d.position v).2))
        (markedMemoryIndependentSource_last hZ d v hv order j)).symm
  · apply markedMemoryState_eq_of_lists
    intro j
    rw [markedMemoryLabeledQueueState_list]
    rw [markedMemoryIndependentMemory, markedMemoryLabeledQueueState_list,
      markedMemoryIndependentQueue_edge hZ d v hv]

theorem markedMemoryIndependentRawEdge_last (v : ℕ) (hv : v < n) (order : J → Equiv.Perm (Fin pads)) :
    markedRawEdgeTargetLast (markedMemoryIndependentMemory hZ d (2*v+1) (by omega))
      (markedMemoryIndependentRawEdge hZ d v hv order).promotions
      (markedMemoryIndependentRawEdge hZ d v hv order).fresh =
      fun j => (d.particle j (d.activeId (v+1) j (markedMemoryIndependentIncoming hZ d v hv j))).1 := by
  refine (markedMemoryEdgeQueueChoice_target_prime hZ (d.position v) (d.position (v+1))
    (markedMemoryIndependentSlottedActive hZ d v hv order)
    (markedMemoryIndependentQueue hZ d (2*v+1))
    (markedMemoryIndependentQueue_nodup hZ d (2*v+1) (by omega))
    (fun j => (d.lifespan j).incoming (2*v+1)) (fun j => (d.lifespan j).outgoing (2*v+1))
    (fun j => decide (2*v+1 < (d.lifespan j).last ((d.lifespan j).outgoing (2*v+1)))) d.particle
    (markedMemoryIndependentQueue_bound hZ d (2*v+1) (by omega))
    (markedMemoryIndependentPromotion_hits hZ d v hv) (markedMemoryIndependentEdge_bound hZ d v hv)).trans ?_
  funext j
  rw [markedMemoryIndependentIncoming_eq]

def markedMemoryIndependentEdge (v : ℕ) (hv : v < n) (order : J → Equiv.Perm (Fin pads)) :
    MarkedMemoryEdgeChoice hZ (markedMemoryIndependentPostGhost hZ d v (Nat.le_of_lt hv)) :=
  ⟨markedMemoryIndependentSourceSlots hZ d v hv order,
    markedMemoryIndependentRawEdge hZ d v hv order,
    markedMemoryIndependentTargetSlots hZ d v hv order⟩

/-- The literal edge has precisely the next independent vertex state,
for every retained copied-slot order. -/
theorem markedMemoryIndependentEdge_target (v : ℕ) (hv : v < n) (order : J → Equiv.Perm (Fin pads)) :
    markedMemoryEdgeChoiceTarget hZ (markedMemoryIndependentPostGhost hZ d v (Nat.le_of_lt hv))
      (markedMemoryIndependentEdge hZ d v hv order) =
        markedMemoryIndependentState hZ d (v+1) hv := by
  have he := markedMemoryIdentity_slotChoice_target (fun j a => (d.particle j a).1)
    (d.activeId v) (d.activeId (v+1)) (markedMemoryIndependentOutgoing hZ d v hv)
    (markedMemoryIndependentIncoming hZ d v hv) hZ (d.position v) (d.position (v+1))
    (markedMemoryIndependentMemory hZ d (2*v+1) (by omega))
    (markedMemoryIndependentMemory hZ d (2*(v+1)) (by omega))
    (markedMemoryIndependentSlotPairs hZ d v hv order) (markedMemoryIndependentRawEdge hZ d v hv order)
    rfl (markedMemoryIndependentRawEdge_memory hZ d v hv order)
    (markedMemoryIndependentRawEdge_last hZ d v hv order)
  exact (congrArg (markedRawSlotEquiv (markedMemoryIndependentTargetSlots hZ d v hv order)) he).trans
    ((markedRawSlotEquiv (markedMemoryIndependentTargetSlots hZ d v hv order)).apply_symm_apply _)

end
end ArtinMatthews
