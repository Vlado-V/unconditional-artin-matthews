module

public import ArtinMatthews.MarkedMemoryActualEdgeQueueLists


set_option backward.privateInPublic true
@[expose] public section

/-! The actual ordered pending queue follows the independent edge queue
recurrence: delete only the promoted incoming identity, retain all other
old indices in order, then append the outgoing identity exactly when its
computed lifespan continues. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s) (v : Fin n)

local notation "edge" => markedMemoryHistoryVertexEdge hZ history v
local notation "source" => markedMemoryGhostChoiceTarget hZ
  (markedMemoryHistoryVertexState hZ history v.castSucc) (markedMemoryHistoryVertexGhost hZ history v.castSucc)
local notation "time" => 2*v.val+1

theorem markedMemoryActualEdge_survivor_iff (j : J) (k : Fin (source.2.2.1.1 j : ℕ)) :
    k ∈ markedRawGhostSurvivors source.2.2 (markedRawEdgePromotionDeletion edge.2.1.promotions) j ↔
      markedMemoryActualEdgeSourcePendingIds hZ history v j k ≠ markedMemoryActualIncoming hZ history v j := by
  constructor
  · intro hk he
    have hp := (markedMemoryActualEdge_promote_iff hZ history v j k).mpr he
    have hn : k ∉ (edge.2.1.promotions j).toFinset := (Finset.mem_sdiff.mp hk).2
    exact hn (Option.mem_toFinset.mpr (Option.mem_def.mpr hp))
  · intro hn
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro hk
    exact hn ((markedMemoryActualEdge_promote_iff hZ history v j k).mp
      (Option.mem_def.mp (Option.mem_toFinset.mp hk)))

theorem markedMemoryActualEdge_survivor_list (j : J) :
    List.ofFn (fun k => markedMemoryActualEdgeSourcePendingIds hZ history v j
      ((markedRawGhostSurvivors source.2.2 (markedRawEdgePromotionDeletion edge.2.1.promotions) j).orderEmbOfFin rfl k)) =
      (markedMemoryActualPendingQueue hZ history time j).filter
        (fun a => decide (a ≠ markedMemoryActualIncoming hZ history v j)) := by
  have h := markedMemoryOfFn_filter (markedMemoryActualEdgeSourcePendingIds hZ history v j)
    (markedRawGhostSurvivors source.2.2 (markedRawEdgePromotionDeletion edge.2.1.promotions) j)
    (fun a => a ≠ markedMemoryActualIncoming hZ history v j)
    (markedMemoryActualEdge_survivor_iff hZ history v j)
  rw [markedMemoryActualEdgeSourcePendingIds_list] at h
  exact h

theorem markedMemoryActualEdge_store_list (j : J) :
    List.ofFn (fun _ : Fin (if edge.2.1.store j then 1 else 0) =>
      markedMemoryActualOutgoing hZ history v j) =
      if edge.2.1.store j then [markedMemoryActualOutgoing hZ history v j] else [] := by
  cases edge.2.1.store j <;> simp

theorem markedMemoryActualEdge_pending_queue (j : J) :
    markedMemoryActualPendingQueue hZ history (time+1) j =
      markedMemoryEdgeQueue (markedMemoryActualPendingQueue hZ history time j)
        (markedMemoryActualIncoming hZ history v j) (markedMemoryActualOutgoing hZ history v j)
        (edge.2.1.store j) := by
  rw [← markedMemoryActualEdgeTargetPendingIds_list hZ history v j,
    markedMemoryActualEdge_pending_append hZ history v j,
    markedMemoryActualEdge_survivor_list hZ history v j,
    markedMemoryActualEdge_store_list hZ history v j]
  rfl

/-- Literal ordered edge recurrence at every actual finite edge time. -/
theorem markedMemoryActualEdge_queue (j : J) :
    markedMemoryActualPendingQueue hZ history ((2*v.val+1)+1) j =
      markedMemoryEdgeQueue (markedMemoryActualPendingQueue hZ history (2*v.val+1) j)
        (markedMemoryActualIncoming hZ history v j) (markedMemoryActualOutgoing hZ history v j)
        (decide ((2*v.val+1) <
          markedMemoryActualLast hZ history j (markedMemoryActualOutgoing hZ history v j))) := by
  rw [← markedMemoryActualEdge_store_eq_decide_last hZ history v j]
  exact markedMemoryActualEdge_pending_queue hZ history v j

end
end ArtinMatthews
