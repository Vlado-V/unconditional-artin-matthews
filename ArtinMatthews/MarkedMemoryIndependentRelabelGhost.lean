module

public import ArtinMatthews.MarkedMemoryIndependentRelabel
public import ArtinMatthews.MarkedMemoryRelabelIndex
public import ArtinMatthews.MarkedMemoryGhostChoiceRecovery


set_option backward.privateInPublic true
@[expose] public section

/-! Reconstructed ghost operations are unchanged by identity relabeling.
Their exact source-index masks and their complete target states determine
the original ordered birth coordinates. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {A A' : J → Type*}
  [∀ j, DecidableEq (A j)] [∀ j, Fintype (A j)]
  [∀ j, DecidableEq (A' j)] [∀ j, Fintype (A' j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (e : (j : J) → A j ≃ A' j)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)

theorem markedMemoryIndependentRelabel_queue_get (t : ℕ) (j : J)
    (i : Fin (markedMemoryIndependentQueue hZ (markedMemoryIndependentRelabel hZ e d) t j).length)
    (k : Fin (markedMemoryIndependentQueue hZ d t j).length) (hi : i.val = k.val) :
    (e j).symm ((markedMemoryIndependentQueue hZ (markedMemoryIndependentRelabel hZ e d) t j).get i) =
      (markedMemoryIndependentQueue hZ d t j).get k :=
  markedMemoryRelabel_list_get (e j) _ _ (markedMemoryIndependentRelabel_queue hZ e d t j) i k hi

def markedMemoryIndependentRelabelGhostTransport (v : ℕ) (hv : v ≤ n) :
    MarkedMemoryGhostChoice hZ (markedMemoryIndependentState hZ d v hv) :=
  markedMemoryGhostTransport hZ (markedMemoryIndependentRelabel_state hZ e d v hv)
    (markedMemoryIndependentGhost hZ (markedMemoryIndependentRelabel hZ e d) v hv)

theorem markedMemoryIndependentRelabel_ghost_deletion (v : ℕ) (hv : v ≤ n) :
    (markedMemoryIndependentRelabelGhostTransport hZ e d v hv).deletion =
      (markedMemoryIndependentGhost hZ d v hv).deletion := by
  funext j
  apply Finset.ext
  intro k
  rw [markedMemoryIndependentRelabelGhostTransport, markedMemoryGhostTransport_deletion_mem]
  let i : Fin (markedMemoryIndependentQueue hZ (markedMemoryIndependentRelabel hZ e d) (2*v) j).length :=
    Fin.cast (congrArg (fun q : MarkedRawState P (pads+1) B Z => (q.2.2.1.1 j : ℕ))
      (markedMemoryIndependentRelabel_state hZ e d v hv).symm) k
  change i ∈ markedMemoryGhostQueueDeletion
      (markedMemoryIndependentQueue hZ (markedMemoryIndependentRelabel hZ e d) (2*v))
      (fun j => ((markedMemoryIndependentRelabel hZ e d).lifespan j).last) (2*v) j ↔ _
  simp only [markedMemoryGhostQueueDeletion, Finset.mem_filter, Finset.mem_univ, true_and]
  change (d.lifespan j).last ((e j).symm
      ((markedMemoryIndependentQueue hZ (markedMemoryIndependentRelabel hZ e d) (2*v) j).get i)) = 2*v ↔ _
  rw [markedMemoryIndependentRelabel_queue_get hZ e d (2*v) j i k rfl]
  change _ ↔ k ∈ markedMemoryGhostQueueDeletion (markedMemoryIndependentQueue hZ d (2*v))
    (fun j => (d.lifespan j).last) (2*v) j
  constructor
  · intro hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk⟩
  · intro hk
    exact (Finset.mem_filter.mp hk).2

theorem markedMemoryIndependentRelabel_ghost_target (v : ℕ) (hv : v ≤ n) :
    markedMemoryGhostChoiceTarget hZ _ (markedMemoryIndependentRelabelGhostTransport hZ e d v hv) =
      markedMemoryGhostChoiceTarget hZ _ (markedMemoryIndependentGhost hZ d v hv) := by
  rw [markedMemoryIndependentRelabelGhostTransport, markedMemoryGhostTransport_target,
    markedMemoryIndependentGhost_target, markedMemoryIndependentRelabel_postGhost,
    markedMemoryIndependentGhost_target]

theorem markedMemoryIndependentRelabel_ghost_eq (v : ℕ) (hv : v ≤ n) :
    markedMemoryIndependentRelabelGhostTransport hZ e d v hv = markedMemoryIndependentGhost hZ d v hv :=
  markedMemoryGhostChoice_eq_of_deletion_target hZ _ _
    (markedMemoryIndependentRelabel_ghost_deletion hZ e d v hv)
    (markedMemoryIndependentRelabel_ghost_target hZ e d v hv)

theorem markedMemoryIndependentRelabel_ghost_heq (v : ℕ) (hv : v ≤ n) :
    HEq (markedMemoryIndependentGhost hZ (markedMemoryIndependentRelabel hZ e d) v hv)
      (markedMemoryIndependentGhost hZ d v hv) :=
  (markedMemoryGhostTransport_heq hZ (markedMemoryIndependentRelabel_state hZ e d v hv) _).trans
    (heq_of_eq (markedMemoryIndependentRelabel_ghost_eq hZ e d v hv))

end
end ArtinMatthews
