module

public import ArtinMatthews.MarkedMemoryLifespanQueueSchedule
public import ArtinMatthews.MarkedMemoryQueueState


set_option backward.privateInPublic true
@[expose] public section

/-! Turn independent per-band lifespan queues into the actual total-
truncated raw memory. The cutoff is the sum over all bands, and equal
numeric particle values are retained as separate ordered entries. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j, DecidableEq (A j)] [∀ j, Fintype (A j)]
  {P : J → Finset Nat.Primes} {H B : ℕ}

theorem markedMemoryGroupedPendingQueue_length
    (d : (j : J) → MarkedMemoryQueueLifespanData (A j) H) (t : ℕ) (ht : t ≤ H) :
    (∑ j, (markedMemoryPendingQueueAt (d j) t).length) =
      ∑ j, (markedMemoryPendingIdentitySet (d j) t).card := by
  apply Finset.sum_congr rfl
  intro j _
  exact markedMemoryPendingQueueAt_length (d j) t ht

theorem markedMemoryGroupedPendingQueue_bound
    (d : (j : J) → MarkedMemoryQueueLifespanData (A j) H) (t : ℕ) (ht : t ≤ H)
    (hB : (∑ j, (markedMemoryPendingIdentitySet (d j) t).card) ≤ B) :
    (∑ j, (markedMemoryPendingQueueAt (d j) t).length) ≤ B := by
  rwa [markedMemoryGroupedPendingQueue_length d t ht]

def markedMemoryLifespanQueueMemory
    (d : (j : J) → MarkedMemoryQueueLifespanData (A j) H)
    (particle : (j : J) → A j → MarkedRawParticle (P j)) (t : ℕ) (ht : t ≤ H)
    (hB : (∑ j, (markedMemoryPendingIdentitySet (d j) t).card) ≤ B) : MarkedRawMemory P B :=
  markedMemoryQueueState (fun j => (markedMemoryPendingQueueAt (d j) t).map (particle j))
    (by simpa only [List.length_map] using markedMemoryGroupedPendingQueue_bound d t ht hB)

theorem markedMemoryLifespanQueueMemory_list
    (d : (j : J) → MarkedMemoryQueueLifespanData (A j) H)
    (particle : (j : J) → A j → MarkedRawParticle (P j)) (t : ℕ) (ht : t ≤ H)
    (hB : (∑ j, (markedMemoryPendingIdentitySet (d j) t).card) ≤ B) (j : J) :
    List.ofFn ((markedMemoryLifespanQueueMemory d particle t ht hB).2 j) =
      (markedMemoryPendingQueueAt (d j) t).map (particle j) :=
  markedMemoryQueueState_list _ _ j

theorem markedMemoryLifespanQueueMemory_size
    (d : (j : J) → MarkedMemoryQueueLifespanData (A j) H)
    (particle : (j : J) → A j → MarkedRawParticle (P j)) (t : ℕ) (ht : t ≤ H)
    (hB : (∑ j, (markedMemoryPendingIdentitySet (d j) t).card) ≤ B) (j : J) :
    ((markedMemoryLifespanQueueMemory d particle t ht hB).1.1 j : ℕ) =
      (markedMemoryPendingIdentitySet (d j) t).card := by
  change ((markedMemoryPendingQueueAt (d j) t).map (particle j)).length = _
  rw [List.length_map, markedMemoryPendingQueueAt_length (d j) t ht]

end
end ArtinMatthews
