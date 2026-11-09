module

public import ArtinMatthews.MarkedMemoryIndependentRelabelSlots
public import ArtinMatthews.MarkedMemoryIndependentRelabelGhost
public import ArtinMatthews.MarkedMemoryRawEdgeRecovery
public import ArtinMatthews.MarkedMemoryChoiceExt


set_option backward.privateInPublic true
@[expose] public section

/-! Literal reconstructed edge choices are invariant under identity
relabeling, including old-only promotion indices, fresh primes and both
slot permutations for the same copied order. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {A A' : J → Type*}
  [∀ j, DecidableEq (A j)] [∀ j, Fintype (A j)]
  [∀ j, DecidableEq (A' j)] [∀ j, Fintype (A' j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (e : (j : J) → A j ≃ A' j)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (v : ℕ) (hv : v < n) (order : J → Equiv.Perm (Fin pads))

def markedMemoryIndependentRelabelRawTransport :
    MarkedRawEdgeChoice hZ (markedRawSlotEquiv (markedMemoryIndependentSourceSlots hZ d v hv order)
      (markedMemoryIndependentPostGhost hZ d v (Nat.le_of_lt hv))) :=
  markedMemoryRawEdgeTransport hZ (markedMemoryIndependentRelabel_rawSource hZ e d v hv order)
    (markedMemoryIndependentRawEdge hZ (markedMemoryIndependentRelabel hZ e d) v hv order)

theorem markedMemoryIndependentRelabel_raw_target :
    (markedMemoryIndependentRelabelRawTransport hZ e d v hv order).target =
      (markedMemoryIndependentRawEdge hZ d v hv order).target := by
  rw [markedMemoryIndependentRelabelRawTransport, markedMemoryRawEdgeTransport_target]
  rfl

theorem markedMemoryIndependentRelabel_raw_store :
    (markedMemoryIndependentRelabelRawTransport hZ e d v hv order).store =
      (markedMemoryIndependentRawEdge hZ d v hv order).store := by
  rw [markedMemoryIndependentRelabelRawTransport, markedMemoryRawEdgeTransport_store]
  funext j
  change decide (2*v+1 < (d.lifespan j).last ((e j).symm (e j ((d.lifespan j).outgoing (2*v+1))))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem markedMemoryIndependentRelabel_raw_promotions :
    (markedMemoryIndependentRelabelRawTransport hZ e d v hv order).promotions =
      (markedMemoryIndependentRawEdge hZ d v hv order).promotions := by
  funext j
  apply Option.ext
  intro k
  rw [markedMemoryIndependentRelabelRawTransport, markedMemoryRawEdgeTransport_promotions_some]
  let i : Fin (markedMemoryIndependentQueue hZ (markedMemoryIndependentRelabel hZ e d) (2*v+1) j).length :=
    Fin.cast (congrArg (fun q : MarkedRawState P (pads+1) B Z => (q.2.2.1.1 j : ℕ))
      (markedMemoryIndependentRelabel_rawSource hZ e d v hv order).symm) k
  change (markedMemoryIndependentRawEdge hZ (markedMemoryIndependentRelabel hZ e d) v hv order).promotions j = some i ↔ _
  refine (markedMemoryEdgeQueuePromotion_eq_some
    (markedMemoryIndependentQueue hZ (markedMemoryIndependentRelabel hZ e d) (2*v+1))
    (markedMemoryIndependentQueue_nodup hZ (markedMemoryIndependentRelabel hZ e d) (2*v+1) (by omega))
    (fun j => ((markedMemoryIndependentRelabel hZ e d).lifespan j).incoming (2*v+1)) j i).trans ?_
  refine Iff.trans ?_ (markedMemoryEdgeQueuePromotion_eq_some
    (markedMemoryIndependentQueue hZ d (2*v+1))
    (markedMemoryIndependentQueue_nodup hZ d (2*v+1) (by omega))
    (fun j => (d.lifespan j).incoming (2*v+1)) j k).symm
  change (markedMemoryIndependentQueue hZ (markedMemoryIndependentRelabel hZ e d) (2*v+1) j).get i =
      e j ((d.lifespan j).incoming (2*v+1)) ↔
    (markedMemoryIndependentQueue hZ d (2*v+1) j).get k = (d.lifespan j).incoming (2*v+1)
  have hget := markedMemoryIndependentRelabel_queue_get hZ e d (2*v+1) j i k rfl
  constructor
  · intro hi
    simpa only [Equiv.symm_apply_apply] using hget.symm.trans (congrArg (e j).symm hi)
  · intro hk
    apply (e j).symm.injective
    simpa only [Equiv.symm_apply_apply] using hget.trans hk

theorem markedMemoryIndependentRelabel_raw_last :
    markedRawEdgeTargetLast _ (markedMemoryIndependentRelabelRawTransport hZ e d v hv order).promotions
      (markedMemoryIndependentRelabelRawTransport hZ e d v hv order).fresh =
    markedRawEdgeTargetLast _ (markedMemoryIndependentRawEdge hZ d v hv order).promotions
      (markedMemoryIndependentRawEdge hZ d v hv order).fresh := by
  rw [markedMemoryIndependentRelabelRawTransport, markedMemoryRawEdgeTransport_last]
  change markedRawEdgeTargetLast
      (markedMemoryIndependentMemory hZ (markedMemoryIndependentRelabel hZ e d) (2*v+1) (by omega))
      (markedMemoryIndependentRawEdge hZ (markedMemoryIndependentRelabel hZ e d) v hv order).promotions
      (markedMemoryIndependentRawEdge hZ (markedMemoryIndependentRelabel hZ e d) v hv order).fresh =
    markedRawEdgeTargetLast (markedMemoryIndependentMemory hZ d (2*v+1) (by omega))
      (markedMemoryIndependentRawEdge hZ d v hv order).promotions
      (markedMemoryIndependentRawEdge hZ d v hv order).fresh
  rw [markedMemoryIndependentRawEdge_last hZ (markedMemoryIndependentRelabel hZ e d) v hv order,
    markedMemoryIndependentRawEdge_last hZ d v hv order]
  funext j
  rw [markedMemoryIndependentRelabel_incoming]
  change (d.particle j ((e j).symm (e j (d.activeId (v+1) j (markedMemoryIndependentIncoming hZ d v hv j))))).1 = _
  rw [Equiv.symm_apply_apply]

theorem markedMemoryIndependentRelabel_raw_eq :
    markedMemoryIndependentRelabelRawTransport hZ e d v hv order =
      markedMemoryIndependentRawEdge hZ d v hv order :=
  markedMemoryRawEdgeChoice_eq_of_last hZ _ _
    (markedMemoryIndependentRelabel_raw_target hZ e d v hv order)
    (markedMemoryIndependentRelabel_raw_store hZ e d v hv order)
    (markedMemoryIndependentRelabel_raw_promotions hZ e d v hv order)
    (markedMemoryIndependentRelabel_raw_last hZ e d v hv order)

theorem markedMemoryIndependentRelabel_raw_heq :
    HEq (markedMemoryIndependentRawEdge hZ (markedMemoryIndependentRelabel hZ e d) v hv order)
      (markedMemoryIndependentRawEdge hZ d v hv order) :=
  (markedMemoryRawEdgeTransport_heq hZ (markedMemoryIndependentRelabel_rawSource hZ e d v hv order) _).trans
    (heq_of_eq (markedMemoryIndependentRelabel_raw_eq hZ e d v hv order))

theorem markedMemoryIndependentRelabel_edge_heq :
    HEq (markedMemoryIndependentEdge hZ (markedMemoryIndependentRelabel hZ e d) v hv order)
      (markedMemoryIndependentEdge hZ d v hv order) :=
  markedMemoryEdgeChoice_heq_of_fields hZ
    (markedMemoryIndependentRelabel_postGhost hZ e d v (Nat.le_of_lt hv)) _ _
    (markedMemoryIndependentRelabel_sourceSlots hZ e d v hv order)
    (markedMemoryIndependentRelabel_raw_heq hZ e d v hv order)
    (markedMemoryIndependentRelabel_targetSlots hZ e d v hv order)

end
end ArtinMatthews
