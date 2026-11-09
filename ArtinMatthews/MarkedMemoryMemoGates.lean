module

public import ArtinMatthews.MarkedMemoryGhostMemo
public import ArtinMatthews.MarkedMemoryEdgeMemo


set_option backward.privateInPublic true
@[expose] public section

/-! The actual permutation event implies each chronological stage gate.
Every gate uses the exact memo before that stage and its literal ordered
birth tuple. The completed memo recovers all potential-address values. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}

omit [DecidableEq J] in
theorem markedMemoryHistoryMemo_full
    (history : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryHistoryMemo hZ history (2*n+2)=markedMemoryPotentialAddressValue hZ history := by
  funext a
  apply markedMemoryPotentialMemo_prior
  rcases a with ⟨j,k⟩ | ⟨t,j,k⟩ | ⟨t,j⟩ <;>
    simp only [markedMemoryPotentialChronologicalTime] <;> omega

theorem markedMemoryHistory_initial_stageGate
    (history : MarkedMemoryChronologicalHistory hZ n s)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B n))
    (hσ : MarkedBirthPermutationEvent (markedMemoryPotentialAddressValue hZ history) σ) :
    markedMemoryStageBirthGate σ 0 (markedMemoryHistoryMemo hZ history 0)
      markedMemoryInitialDraw markedMemoryInitialDraw_injective
      (fun a : Σ _j : J,Fin (pads+1) => s.2.1 a.1 a.2) := by
  apply markedMemoryStageBirthGate_of_memo_event 0 _ σ hσ
  exact markedMemoryHistoryMemo_initial hZ history

theorem markedMemoryHistory_ghost_stageGate
    (history : MarkedMemoryChronologicalHistory hZ n s)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B n))
    (hσ : MarkedBirthPermutationEvent (markedMemoryPotentialAddressValue hZ history) σ)
    (v : Fin (n+1)) :
    let ghost := markedMemoryHistoryVertexGhost hZ history v
    markedMemoryStageBirthGate σ (2*v.val+1) (markedMemoryHistoryMemo hZ history (2*v.val+1))
      (markedMemoryGhostStageDraw v ghost.sizes.1)
      (markedMemoryGhostStageDraw_injective v ghost.sizes.1)
      (fun a : Σ j,Fin (ghost.sizes.1 j:ℕ) => ghost.births a.1 a.2) := by
  dsimp only
  apply markedMemoryStageBirthGate_of_memo_event (2*v.val+1) _ σ hσ
  exact markedMemoryHistoryMemo_ghost hZ history v

theorem markedMemoryHistory_edge_stageGate
    (history : MarkedMemoryChronologicalHistory hZ n s)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B n))
    (hσ : MarkedBirthPermutationEvent (markedMemoryPotentialAddressValue hZ history) σ)
    (v : Fin n) :
    let edge := markedMemoryHistoryVertexEdge hZ history v
    let pre := markedMemoryGhostChoiceTarget hZ (markedMemoryHistoryVertexState hZ history v.castSucc)
      (markedMemoryHistoryVertexGhost hZ history v.castSucc)
    let source := markedRawSlotEquiv edge.1 pre
    let I := markedDirtyEdgePromotedGroups edge.2.1.promotions
    markedMemoryStageBirthGate σ (2*v.val+2) (markedMemoryHistoryMemo hZ history (2*v.val+2))
      (markedMemoryEdgeStageDraw v I) (markedMemoryEdgeStageDraw_injective v I)
      (markedDirtyFixedEdgeChoiceCode hZ source I ⟨edge.2.1,rfl⟩).2.2.2 := by
  dsimp only
  apply markedMemoryStageBirthGate_of_memo_event (2*v.val+2) _ σ hσ
  exact markedMemoryHistoryMemo_edge hZ history v

end
end ArtinMatthews
