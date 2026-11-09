module

public import ArtinMatthews.MarkedMemoryActualStateReconstruction
public import ArtinMatthews.MarkedMemoryGhostChoiceRecovery


set_option backward.privateInPublic true
@[expose] public section

/-! The independently reconstructed ghost is the original literal
choice, including its ordered birth tuple. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s)
  (ha : MarkedMemoryHistoryAnchorAdmissible hZ history)

local notation "tableau" => markedMemoryActualTableau hZ history ha
local notation "vertex" v:max => markedMemoryHistoryVertexState hZ history v
local notation "ghost" v:max => markedMemoryHistoryVertexGhost hZ history v

theorem markedMemoryActualTableau_ghost_source (v : Fin (n+1)) :
    markedMemoryIndependentState hZ tableau v.val (by omega) = vertex v :=
  (markedMemoryActualTableau_state hZ history ha v.val (by omega)).trans
    (markedMemoryHistoryVertexState_trace hZ history v)

theorem markedMemoryActualTableau_ghost_heq (v : Fin (n+1)) :
    HEq (markedMemoryIndependentGhost hZ tableau v.val (by omega)) (ghost v) := by
  let c := markedMemoryIndependentGhost hZ tableau v.val (by omega)
  let hs := markedMemoryActualTableau_ghost_source hZ history ha v
  have hd : (markedMemoryGhostTransport hZ hs c).deletion = (ghost v).deletion := by
    funext j
    apply Finset.ext
    intro k
    rw [markedMemoryGhostTransport_deletion_mem]
    let q := markedMemoryIndependentQueue hZ tableau (2*v.val) j
    let i : Fin q.length := Fin.cast
      (congrArg (fun r : MarkedRawState P (pads+1) B Z => (r.2.2.1.1 j : ℕ)) hs.symm) k
    have ht : markedMemoryHistoryGhostTime n v = 2*v.val := markedMemoryHistoryGhostTime_eq n v
    have hq : q = List.ofFn (markedMemoryActualGhostSourceIds hZ history v j) := by
      exact (markedMemoryActualTableau_queue hZ history ha (2*v.val) (by omega) j).trans
        (by simpa only [ht] using (markedMemoryActualGhostSourceIds_list hZ history v j).symm)
    have hi := markedMemoryListGet_ofFn_eq (markedMemoryActualGhostSourceIds hZ history v j) q hq.symm i
    have hk : Fin.cast (by rw [hq,List.length_ofFn]) i = k := Fin.ext rfl
    rw [hk] at hi
    change i ∈ markedMemoryGhostQueueDeletion (markedMemoryIndependentQueue hZ tableau (2*v.val))
      (fun j => ((tableau).lifespan j).last) (2*v.val) j ↔ k ∈ (ghost v).deletion j
    simp only [markedMemoryGhostQueueDeletion,Finset.mem_filter,Finset.mem_univ,true_and]
    change markedMemoryActualLast hZ history j (q.get i) = 2*v.val ↔ k ∈ (ghost v).deletion j
    rw [hi]
    simpa only [ht] using (markedMemoryActualGhost_deleted_iff hZ history v j k).symm
  have ht : markedMemoryGhostChoiceTarget hZ (vertex v) (markedMemoryGhostTransport hZ hs c) =
      markedMemoryGhostChoiceTarget hZ (vertex v) (ghost v) := by
    rw [markedMemoryGhostTransport_target]
    exact (markedMemoryIndependentGhost_target hZ tableau v.val (by omega)).trans
      ((markedMemoryActualTableau_postGhost hZ history ha v.val (by omega)).trans
        (by simpa only [markedMemoryHistoryGhostTime_eq] using markedMemoryHistoryGhostTarget_trace hZ history v))
  have hc := markedMemoryGhostChoice_eq_of_deletion_target hZ (markedMemoryGhostTransport hZ hs c) (ghost v) hd ht
  exact (markedMemoryGhostTransport_heq hZ hs c).trans (heq_of_eq hc)

end
end ArtinMatthews
