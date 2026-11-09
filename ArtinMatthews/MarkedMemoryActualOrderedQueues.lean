module

public import ArtinMatthews.MarkedMemoryActualGhostQueue
public import ArtinMatthews.MarkedMemoryActualQueueData
public import ArtinMatthews.MarkedMemoryActualEdgeQueue


set_option backward.privateInPublic true
@[expose] public section

/-! The independently reconstructed queue equals the literal ordered
pending queue at every bounded half-step of the original history. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s)

theorem markedMemoryActualQueueData_order (t : ℕ) (ht : t ≤ 2*n+1) (j : J) :
    markedMemoryPendingQueueAt (markedMemoryActualQueueData hZ history j) t =
      markedMemoryActualPendingQueue hZ history t j := by
  induction t with
  | zero => rfl
  | succ t ih =>
    by_cases he : t % 2 = 0
    · simp only [markedMemoryPendingQueueAt,he,ite_true]
      change markedMemoryGhostQueue (markedMemoryPendingQueueAt (markedMemoryActualQueueData hZ history j) t)
        (markedMemoryActualBirthQueue hZ history t j) (markedMemoryActualLast hZ history j) t = _
      rw [ih (by omega)]
      let v : Fin (n+1) := ⟨t/2,by omega⟩
      have hv : markedMemoryHistoryGhostTime n v = t := by
        rw [markedMemoryHistoryGhostTime_eq]
        change 2*(t/2) = t
        omega
      simpa only [hv] using (markedMemoryActualGhost_queue hZ history v j).symm
    · have ho : t % 2 = 1 := by omega
      simp only [markedMemoryPendingQueueAt,he,ite_false]
      change markedMemoryEdgeQueue (markedMemoryPendingQueueAt (markedMemoryActualQueueData hZ history j) t)
        (markedMemoryActualIncomingAt hZ history t j) (markedMemoryActualOutgoingAt hZ history t j)
        (decide (t < markedMemoryActualLast hZ history j (markedMemoryActualOutgoingAt hZ history t j))) = _
      rw [ih (by omega)]
      obtain ⟨v,hv⟩ := markedMemoryActualOddIndex (n := n) t (by omega) ho
      rw [hv,markedMemoryActualIncomingAt_edge,markedMemoryActualOutgoingAt_edge]
      exact (markedMemoryActualEdge_queue hZ history v j).symm

end
end ArtinMatthews
