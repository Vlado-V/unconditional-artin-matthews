module

public import ArtinMatthews.MarkedMemoryStageMemo
public import ArtinMatthews.MarkedMemoryHistoryPotentialAccess


set_option backward.privateInPublic true
@[expose] public section

/-! Initial active labels and literal ordered ghost births produce the
actual history memo. Unperformed ghost slots are proved absent, rather
than assigned a prime or removed from the potential-address carrier. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}

theorem markedMemoryHistoryMemo_initial
    (history : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryStageBirthValues 0 (markedMemoryHistoryMemo hZ history 0)
      markedMemoryInitialDraw markedMemoryInitialDraw_injective
      (fun a : Σ _j : J,Fin (pads+1) => s.2.1 a.1 a.2)=
        markedMemoryHistoryMemo hZ history 1 := by
  classical
  apply markedMemoryStageBirthValues_memo
  · intro a
    rfl
  · intro a
    rfl
  · intro a ht hn
    rcases a with ⟨j,k⟩ | ⟨t,j,k⟩ | ⟨t,j⟩
    · exact False.elim (hn (markedMemoryStageDraw_mem
        markedMemoryInitialDraw markedMemoryInitialDraw_injective ⟨j,k⟩))
    · simp only [markedMemoryPotentialChronologicalTime] at ht
      omega
    · simp only [markedMemoryPotentialChronologicalTime] at ht
      omega

theorem markedMemoryHistoryMemo_ghost
    (history : MarkedMemoryChronologicalHistory hZ n s) (v : Fin (n+1)) :
    let ghost := markedMemoryHistoryVertexGhost hZ history v
    markedMemoryStageBirthValues (2*v.val+1) (markedMemoryHistoryMemo hZ history (2*v.val+1))
      (markedMemoryGhostStageDraw v ghost.sizes.1)
      (markedMemoryGhostStageDraw_injective v ghost.sizes.1)
      (fun a : Σ j,Fin (ghost.sizes.1 j:ℕ) => ghost.births a.1 a.2)=
        markedMemoryHistoryMemo hZ history ((2*v.val+1)+1) := by
  classical
  dsimp only
  apply markedMemoryStageBirthValues_memo
  · intro a
    rfl
  · intro a
    exact markedMemoryPotentialGhostValue_vertex_birth hZ history v a.1 a.2
  · intro a ht hn
    rcases a with ⟨j,k⟩ | ⟨w,j,k⟩ | ⟨w,j⟩
    · simp only [markedMemoryPotentialChronologicalTime] at ht
      omega
    · have hw : w=v := Fin.ext (by
        simp only [markedMemoryPotentialChronologicalTime] at ht
        omega)
      subst w
      have hk : ¬k.val < ((markedMemoryHistoryVertexGhost hZ history v).sizes.1 j:ℕ) := by
        intro hk
        apply hn
        exact markedMemoryStageDraw_mem _ (markedMemoryGhostStageDraw_injective v _)
          ⟨j,⟨k.val,hk⟩⟩
      exact markedMemoryPotentialGhostValue_vertex_absent hZ history v j k hk
    · simp only [markedMemoryPotentialChronologicalTime] at ht
      omega

end
end ArtinMatthews
