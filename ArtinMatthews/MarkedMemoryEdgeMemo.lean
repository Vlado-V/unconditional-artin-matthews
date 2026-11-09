module

public import ArtinMatthews.MarkedMemoryStageMemo
public import ArtinMatthews.MarkedMemoryHistoryPotentialAccess
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeFixedCode


set_option backward.privateInPublic true
@[expose] public section

/-! The actual edge inserts precisely its fresh target-last prime
labels. Promoted groups keep the potential edge address at none, while
both source and target slot permutations remain in the literal choice. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}

theorem markedMemoryHistoryMemo_edge
    (history : MarkedMemoryChronologicalHistory hZ n s) (v : Fin n) :
    let edge := markedMemoryHistoryVertexEdge hZ history v
    let pre := markedMemoryGhostChoiceTarget hZ (markedMemoryHistoryVertexState hZ history v.castSucc)
      (markedMemoryHistoryVertexGhost hZ history v.castSucc)
    let source := markedRawSlotEquiv edge.1 pre
    let I := markedDirtyEdgePromotedGroups edge.2.1.promotions
    markedMemoryStageBirthValues (2*v.val+2) (markedMemoryHistoryMemo hZ history (2*v.val+2))
      (markedMemoryEdgeStageDraw v I) (markedMemoryEdgeStageDraw_injective v I)
      (markedDirtyFixedEdgeChoiceCode hZ source I ⟨edge.2.1,rfl⟩).2.2.2=
        markedMemoryHistoryMemo hZ history ((2*v.val+2)+1) := by
  classical
  dsimp only
  let edge := markedMemoryHistoryVertexEdge hZ history v
  let pre := markedMemoryGhostChoiceTarget hZ (markedMemoryHistoryVertexState hZ history v.castSucc)
    (markedMemoryHistoryVertexGhost hZ history v.castSucc)
  let source := markedRawSlotEquiv edge.1 pre
  let I := markedDirtyEdgePromotedGroups edge.2.1.promotions
  change markedMemoryStageBirthValues (2*v.val+2) (markedMemoryHistoryMemo hZ history (2*v.val+2))
      (markedMemoryEdgeStageDraw v I) (markedMemoryEdgeStageDraw_injective v I)
      (markedDirtyFixedEdgeChoiceCode hZ source I ⟨edge.2.1,rfl⟩).2.2.2=
    markedMemoryHistoryMemo hZ history ((2*v.val+2)+1)
  apply markedMemoryStageBirthValues_memo
  · intro i
    rfl
  · intro i
    have hi : edge.2.1.promotions i.1=none := by
      by_contra hn
      exact (Finset.mem_sdiff.mp i.2).2
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩)
    change markedMemoryPotentialEdgeValue hZ history v i.1=
      some ((markedRawEdgeTargetLast source.2.2 edge.2.1.promotions edge.2.1.fresh i.1).1)
    rw [markedMemoryPotentialEdgeValue_vertex]
    exact ite_eq_left hi
  · intro a ht hn
    rcases a with ⟨j,k⟩ | ⟨w,j,k⟩ | ⟨w,j⟩
    · simp only [markedMemoryPotentialChronologicalTime] at ht
      omega
    · simp only [markedMemoryPotentialChronologicalTime] at ht
      omega
    · have hw : w=v := Fin.ext (by
        simp only [markedMemoryPotentialChronologicalTime] at ht
        omega)
      subst w
      have hp : edge.2.1.promotions j≠none := by
        intro hp
        apply hn
        have hj : j∉I := by simp [I,markedDirtyEdgePromotedGroups,hp]
        exact markedMemoryStageDraw_mem _ (markedMemoryEdgeStageDraw_injective v I)
          ⟨j,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hj⟩⟩
      change markedMemoryPotentialEdgeValue hZ history v j=none
      rw [markedMemoryPotentialEdgeValue_vertex]
      exact ite_eq_right hp

end
end ArtinMatthews
