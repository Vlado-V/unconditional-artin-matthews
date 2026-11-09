module

public import ArtinMatthews.MarkedMemoryActualGhostOrigins
public import ArtinMatthews.MarkedMemoryActualGhostTrace
public import ArtinMatthews.MarkedMemoryOfFnFilter


set_option backward.privateInPublic true
@[expose] public section

/-! The ordered ghost queue and birth batch are recovered from the
computed endpoints. No permutation or numeric distinctness is used. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s)

local notation "vertex" v:max => markedMemoryHistoryVertexState hZ history v
local notation "ghost" v:max => markedMemoryHistoryVertexGhost hZ history v

theorem markedMemoryActualGhost_queue_decomp (v : Fin (n+1)) (j : J) :
    markedMemoryActualPendingQueue hZ history ((markedMemoryHistoryGhostTime n v)+1) j =
      List.ofFn (fun k => markedMemoryActualGhostSourceIds hZ history v j
        ((markedRawGhostSurvivors (vertex v).2.2 (ghost v).deletion j).orderEmbOfFin rfl k)) ++
      List.ofFn (markedMemoryActualGhostBirthIds hZ history v j) := by
  rw [← markedMemoryActualGhostTargetIds_list]
  apply (List.map_injective_iff (f := Subtype.val)).mpr Subtype.val_injective
  simp only [List.map_append,List.map_ofFn]
  calc
    _ = List.ofFn (fun k => Sum.elim (markedMemoryHistoryGhostSourceOrigin hZ history v)
        (fun b => markedMemoryHistoryGhostScalarOrigin hZ history ⟨v,Sum.inr b⟩)
        (markedMemoryGhostPopulationOrigin hZ (vertex v) (ghost v) (Sum.inr ⟨j,k⟩))) := by
      congr 1
      funext k
      exact (markedMemoryActualGhostOrigin hZ history v (Sum.inr ⟨j,k⟩)).symm
    _ = _ := by
      rw [markedMemoryGhostOrigin_label_list]
      apply congrArg₂ (fun x y => x ++ y) rfl
      congr 1
      funext k
      exact (markedMemoryActualGhostBirthIds_val hZ history v j k).symm

theorem markedMemoryActualGhostSource_alive (v : Fin (n+1)) (j : J)
    (k : Fin ((vertex v).2.2.1.1 j : ℕ)) :
    markedMemoryActualFirst hZ history j (markedMemoryActualGhostSourceIds hZ history v j k) ≤ (markedMemoryHistoryGhostTime n v) ∧
      (markedMemoryHistoryGhostTime n v) ≤ markedMemoryActualLast hZ history j (markedMemoryActualGhostSourceIds hZ history v j k) := by
  apply (markedMemoryHistory_lifespan_exact hZ history _ ((markedMemoryHistoryGhostTime n v))).mp
  refine ⟨?_,markedMemoryHistoryGhostSourceIndex hZ history v (Sum.inr ⟨j,k⟩),rfl⟩
  rw [markedMemoryHistoryGhostTime_eq]
  have hv := v.isLt
  omega

theorem markedMemoryActualGhostBirth_first (v : Fin (n+1)) (j : J)
    (k : Fin ((ghost v).sizes.1 j : ℕ)) :
    markedMemoryActualFirst hZ history j (markedMemoryActualGhostBirthIds hZ history v j k) = (markedMemoryHistoryGhostTime n v)+1 := by
  unfold markedMemoryActualFirst
  rw [markedMemoryActualGhostBirthIds_val]
  rfl

theorem markedMemoryActualGhost_birthQueue (v : Fin (n+1)) (j : J) :
    markedMemoryActualBirthQueue hZ history ((markedMemoryHistoryGhostTime n v)) j =
      List.ofFn (markedMemoryActualGhostBirthIds hZ history v j) := by
  unfold markedMemoryActualBirthQueue
  rw [markedMemoryActualGhost_queue_decomp,List.filter_append]
  have ho : (List.ofFn (fun k => markedMemoryActualGhostSourceIds hZ history v j
      ((markedRawGhostSurvivors (vertex v).2.2 (ghost v).deletion j).orderEmbOfFin rfl k))).filter
        (fun a => decide (markedMemoryActualFirst hZ history j a = (markedMemoryHistoryGhostTime n v)+1)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp ha
    have hf := (markedMemoryActualGhostSource_alive hZ history v j
      ((markedRawGhostSurvivors (vertex v).2.2 (ghost v).deletion j).orderEmbOfFin rfl k)).1
    simp only [decide_eq_true_eq]
    omega
  have hb : (List.ofFn (markedMemoryActualGhostBirthIds hZ history v j)).filter
      (fun a => decide (markedMemoryActualFirst hZ history j a = (markedMemoryHistoryGhostTime n v)+1)) =
        List.ofFn (markedMemoryActualGhostBirthIds hZ history v j) := by
    apply List.filter_eq_self.mpr
    intro a ha
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp ha
    exact decide_eq_true (markedMemoryActualGhostBirth_first hZ history v j k)
  rw [ho,hb,List.nil_append]

theorem markedMemoryActualGhost_survivorQueue (v : Fin (n+1)) (j : J) :
    List.ofFn (fun k => markedMemoryActualGhostSourceIds hZ history v j
      ((markedRawGhostSurvivors (vertex v).2.2 (ghost v).deletion j).orderEmbOfFin rfl k)) =
    (markedMemoryActualPendingQueue hZ history ((markedMemoryHistoryGhostTime n v)) j).filter
      (fun a => decide ((markedMemoryHistoryGhostTime n v) < markedMemoryActualLast hZ history j a)) := by
  rw [← markedMemoryActualGhostSourceIds_list]
  apply markedMemoryOfFn_filter
  intro k
  have ha := (markedMemoryActualGhostSource_alive hZ history v j k).2
  have hd := markedMemoryActualGhost_deleted_iff hZ history v j k
  simp only [markedRawGhostSurvivors,Finset.mem_sdiff,Finset.mem_univ,true_and]
  rw [hd]
  omega

theorem markedMemoryActualGhost_queue (v : Fin (n+1)) (j : J) :
    markedMemoryActualPendingQueue hZ history ((markedMemoryHistoryGhostTime n v)+1) j =
      markedMemoryGhostQueue (markedMemoryActualPendingQueue hZ history ((markedMemoryHistoryGhostTime n v)) j)
        (markedMemoryActualBirthQueue hZ history ((markedMemoryHistoryGhostTime n v)) j) (markedMemoryActualLast hZ history j) ((markedMemoryHistoryGhostTime n v)) := by
  rw [markedMemoryActualGhost_queue_decomp,markedMemoryActualGhost_survivorQueue,
    ← markedMemoryActualGhost_birthQueue]
  rfl

end
end ArtinMatthews
