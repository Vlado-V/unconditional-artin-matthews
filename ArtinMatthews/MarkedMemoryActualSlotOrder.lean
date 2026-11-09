module

public import ArtinMatthews.MarkedMemoryActualTableau
public import ArtinMatthews.MarkedMemoryIndependentEdge


set_option backward.privateInPublic true
@[expose] public section

/-! The original source and target slot permutations are recovered by
an actual member of the proved slot fiber and its canonical free order. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s)
  (ha : MarkedMemoryHistoryAnchorAdmissible hZ history)

local notation "tableau" => markedMemoryActualTableau hZ history ha
local notation "edge" v:max => markedMemoryHistoryVertexEdge hZ history v

theorem markedMemoryActualTableau_outgoing (v : Fin n) (j : J) :
    markedMemoryIndependentOutgoing hZ tableau v.val v.2 j = (edge v).1 j (Fin.last pads) := by
  apply (markedMemoryActualActiveIds hZ history (2*v.val) j).injective
  have h := markedMemoryIndependentOutgoing_eq hZ tableau v.val v.2 j
  change markedMemoryActualActiveIds hZ history (2*v.val) j _ =
    markedMemoryActualOutgoingAt hZ history (2*v.val+1) j at h
  rw [markedMemoryActualOutgoingAt_edge] at h
  exact h.trans (markedMemoryActualActiveIds_ghost hZ history (2*v.val) (by omega) j _)

theorem markedMemoryActualTableau_incoming (v : Fin n) (j : J) :
    markedMemoryIndependentIncoming hZ tableau v.val v.2 j = ((edge v).2.2 j).symm (Fin.last pads) := by
  apply (markedMemoryActualActiveIds hZ history (2*(v.val+1)) j).injective
  have h := markedMemoryIndependentIncoming_eq hZ tableau v.val v.2 j
  change markedMemoryActualActiveIds hZ history (2*(v.val+1)) j _ =
    markedMemoryActualIncomingAt hZ history (2*v.val+1) j at h
  rw [markedMemoryActualIncomingAt_edge] at h
  have ht : (2*v.val+1)+1 = 2*(v.val+1) := by omega
  simpa only [markedMemoryActualIncoming,ht] using h

def markedMemoryActualSlotPair (v : Fin n) (j : J) :
    MarkedMemorySlotPairFiber ((tableau).activeId v.val j) ((tableau).activeId (v.val+1) j)
      (markedMemoryIndependentOutgoing hZ tableau v.val v.2 j)
      (markedMemoryIndependentIncoming hZ tableau v.val v.2 j) :=
  ⟨⟨(edge v).1 j,(edge v).2.2 j⟩,by
    refine ⟨(markedMemoryActualTableau_outgoing hZ history ha v j).symm,?_,?_⟩
    · rw [markedMemoryActualTableau_incoming]
      exact ((edge v).2.2 j).apply_symm_apply _
    · intro k
      have h := markedMemoryActualEdge_copied hZ history v j k
      rw [markedMemoryActualActiveIds_ghost hZ history (2*v.val) (by omega)] at h
      have ht : (2*v.val+1)+1 = 2*(v.val+1) := by omega
      simpa only [markedMemoryActualTableau,ht] using h⟩

def markedMemoryActualOrder (v : Fin n) (j : J) : Equiv.Perm (Fin pads) :=
  markedMemorySlotPairFiberEquiv ((tableau).activeId v.val j) ((tableau).activeId (v.val+1) j)
    (markedMemoryIndependentOutgoing hZ tableau v.val v.2 j)
    (markedMemoryIndependentIncoming hZ tableau v.val v.2 j)
    (markedMemoryIndependentActive_remaining hZ tableau v.val v.2 j)
    (markedMemoryActualSlotPair hZ history ha v j)

theorem markedMemoryActualOrder_slotPair (v : Fin n) (j : J) :
    markedMemoryIndependentSlotPairs hZ tableau v.val v.2 (markedMemoryActualOrder hZ history ha v) j =
      markedMemoryActualSlotPair hZ history ha v j := by
  exact (markedMemorySlotPairFiberEquiv ((tableau).activeId v.val j) ((tableau).activeId (v.val+1) j)
    (markedMemoryIndependentOutgoing hZ tableau v.val v.2 j)
    (markedMemoryIndependentIncoming hZ tableau v.val v.2 j)
    (markedMemoryIndependentActive_remaining hZ tableau v.val v.2 j)).symm_apply_apply _

theorem markedMemoryActualOrder_sourceSlots (v : Fin n) :
    markedMemoryIndependentSourceSlots hZ tableau v.val v.2 (markedMemoryActualOrder hZ history ha v) = (edge v).1 := by
  funext j
  exact congrArg (fun pair => pair.1.1) (markedMemoryActualOrder_slotPair hZ history ha v j)

theorem markedMemoryActualOrder_targetSlots (v : Fin n) :
    markedMemoryIndependentTargetSlots hZ tableau v.val v.2 (markedMemoryActualOrder hZ history ha v) = (edge v).2.2 := by
  funext j
  exact congrArg (fun pair => pair.1.2) (markedMemoryActualOrder_slotPair hZ history ha v j)

end
end ArtinMatthews
