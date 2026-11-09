module

public import ArtinMatthews.MarkedMemoryActualOrderedQueues
public import ArtinMatthews.MarkedMemoryActualTableau


set_option backward.privateInPublic true
@[expose] public section

/-! Exact original raw states are recovered from the extracted tableau,
including the ordered pending particles. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s)
  (ha : MarkedMemoryHistoryAnchorAdmissible hZ history)

local notation "tableau" => markedMemoryActualTableau hZ history ha

theorem markedMemoryActualTableau_queue (t : ℕ) (ht : t ≤ 2*n+1) (j : J) :
    markedMemoryIndependentQueue hZ tableau t j = markedMemoryActualPendingQueue hZ history t j := by
  have hirr (i₁ i₂ : DecidableEq (MarkedMemoryActualFiber hZ history j)) :
      @markedMemoryPendingQueueAt _ i₁ _ (markedMemoryActualQueueData hZ history j) t =
        @markedMemoryPendingQueueAt _ i₂ _ (markedMemoryActualQueueData hZ history j) t :=
    congrArg (fun i => @markedMemoryPendingQueueAt _ i _ (markedMemoryActualQueueData hZ history j) t)
      (Subsingleton.elim i₁ i₂)
  exact (hirr _ _).trans (markedMemoryActualQueueData_order hZ history t ht j)

theorem markedMemoryActualTableau_memory (t : ℕ) (ht : t ≤ 2*n+1) :
    markedMemoryIndependentMemory hZ tableau t ht = (markedMemoryHistoryTraceState hZ history t).2.2 := by
  apply markedMemoryState_eq_of_lists
  intro j
  rw [markedMemoryIndependentMemory,markedMemoryLabeledQueueState_list]
  change (markedMemoryIndependentQueue hZ tableau t j).map (markedMemoryActualParticle hZ history j) = _
  rw [markedMemoryActualTableau_queue hZ history ha t ht j,markedMemoryActualPendingQueue,List.map_ofFn]
  congr 1
  funext k
  exact markedMemoryActualParticle_pending hZ history ha t j k

theorem markedMemoryActualTableau_state (v : ℕ) (hv : v ≤ n) :
    markedMemoryIndependentState hZ tableau v hv = markedMemoryHistoryTraceState hZ history (2*v) := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · funext j k
    exact congrArg Sigma.fst (markedMemoryActualParticle_active hZ history ha (2*v) j k)
  · exact markedMemoryActualTableau_memory hZ history ha (2*v) (by omega)

omit [DecidableEq J] in
theorem markedMemoryActualTrace_ghost_components (v : ℕ) (hv : v ≤ n) :
    (markedMemoryHistoryTraceState hZ history (2*v+1)).1 = (markedMemoryHistoryTraceState hZ history (2*v)).1 ∧
      (markedMemoryHistoryTraceState hZ history (2*v+1)).2.1 = (markedMemoryHistoryTraceState hZ history (2*v)).2.1 := by
  let w : Fin (n+1) := ⟨v,by omega⟩
  have ht : markedMemoryHistoryGhostTime n w = 2*v := markedMemoryHistoryGhostTime_eq n w
  have hs := markedMemoryHistoryGhostTarget_trace hZ history w
  rw [ht] at hs
  have hsrc := markedMemoryHistoryVertexState_trace hZ history w
  exact ⟨(congrArg Prod.fst hs).trans (congrArg Prod.fst hsrc).symm,
    (congrArg (fun q : MarkedRawState P (pads+1) B Z => q.2.1) hs).trans
      (congrArg (fun q : MarkedRawState P (pads+1) B Z => q.2.1) hsrc).symm⟩

theorem markedMemoryActualTableau_postGhost (v : ℕ) (hv : v ≤ n) :
    markedMemoryIndependentPostGhost hZ tableau v hv = markedMemoryHistoryTraceState hZ history (2*v+1) := by
  have hs := markedMemoryActualTrace_ghost_components hZ history v hv
  apply Prod.ext
  · exact hs.1.symm
  apply Prod.ext
  · change (fun j k => (markedMemoryActualParticle hZ history j (markedMemoryActualActiveIds hZ history (2*v) j k)).1) = _
    rw [hs.2]
    funext j k
    exact congrArg Sigma.fst (markedMemoryActualParticle_active hZ history ha (2*v) j k)
  · exact markedMemoryActualTableau_memory hZ history ha (2*v+1) (by omega)

end
end ArtinMatthews
