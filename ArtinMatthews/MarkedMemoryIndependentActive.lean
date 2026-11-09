module

public import ArtinMatthews.MarkedMemoryIndependentLifespans
public import ArtinMatthews.MarkedMemoryLifespanEdgeQueueTarget


set_option backward.privateInPublic true
@[expose] public section

/-! The active exchange in the independent interval data determines
outgoing and incoming slot indices. Equal active cardinalities force the
remaining identity sets to agree, so compatible slot pairs are constructed
with precisely one free permutation of the copied slots in each band. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j, DecidableEq (A j)] [∀ j, Fintype (A j)]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {n : ℕ}
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)

omit [∀ j, DecidableEq (A j)] in
theorem markedMemoryIndependentOutgoing_exists (v : ℕ) (hv : v < n) (j : J) :
    ∃ i, d.activeId v j i = (d.lifespan j).outgoing (2*v+1) := by
  apply (d.active_mem v (Nat.le_of_lt hv) j _).mp
  apply ((d.lifespan j).ghost_active (2*v) (by omega) (by omega) _).mp
  exact (d.lifespan j).edge_outgoing_active (2*v+1) (by omega) (by omega)

omit [∀ j, DecidableEq (A j)] in
theorem markedMemoryIndependentIncoming_exists (v : ℕ) (hv : v < n) (j : J) :
    ∃ i, d.activeId (v+1) j i = (d.lifespan j).incoming (2*v+1) := by
  apply (d.active_mem (v+1) hv j _).mp
  have he : 2*(v+1) = (2*v+1)+1 := by omega
  rw [he]
  exact ((d.lifespan j).edge_active (2*v+1) (by omega) (by omega) _).mpr (Or.inr rfl)

def markedMemoryIndependentOutgoing (v : ℕ) (hv : v < n) (j : J) : Fin (pads+1) :=
  Classical.choose (markedMemoryIndependentOutgoing_exists hZ d v hv j)

def markedMemoryIndependentIncoming (v : ℕ) (hv : v < n) (j : J) : Fin (pads+1) :=
  Classical.choose (markedMemoryIndependentIncoming_exists hZ d v hv j)

omit [∀ j, DecidableEq (A j)] in
theorem markedMemoryIndependentOutgoing_eq (v : ℕ) (hv : v < n) (j : J) :
    d.activeId v j (markedMemoryIndependentOutgoing hZ d v hv j) = (d.lifespan j).outgoing (2*v+1) :=
  Classical.choose_spec (markedMemoryIndependentOutgoing_exists hZ d v hv j)

omit [∀ j, DecidableEq (A j)] in
theorem markedMemoryIndependentIncoming_eq (v : ℕ) (hv : v < n) (j : J) :
    d.activeId (v+1) j (markedMemoryIndependentIncoming hZ d v hv j) = (d.lifespan j).incoming (2*v+1) :=
  Classical.choose_spec (markedMemoryIndependentIncoming_exists hZ d v hv j)

omit [∀ j, DecidableEq (A j)] in
theorem markedMemoryIndependentActive_exchange (v : ℕ) (hv : v < n) (j : J) (a : A j) :
    (∃ i, d.activeId (v+1) j i = a) ↔
      ((∃ i, d.activeId v j i = a) ∧ a ≠ d.activeId v j (markedMemoryIndependentOutgoing hZ d v hv j)) ∨
        a = d.activeId (v+1) j (markedMemoryIndependentIncoming hZ d v hv j) := by
  rw [← d.active_mem (v+1) hv j a]
  have he : 2*(v+1) = (2*v+1)+1 := by omega
  rw [he, (d.lifespan j).edge_active (2*v+1) (by omega) (by omega),
    (d.lifespan j).ghost_active (2*v) (by omega) (by omega), d.active_mem v (Nat.le_of_lt hv),
    markedMemoryIndependentOutgoing_eq, markedMemoryIndependentIncoming_eq]

theorem markedMemoryIndependentActive_remaining (v : ℕ) (hv : v < n) (j : J) :
    (markedMemoryBirthBatch (d.activeId v j)).erase
        (d.activeId v j (markedMemoryIndependentOutgoing hZ d v hv j)) =
      (markedMemoryBirthBatch (d.activeId (v+1) j)).erase
        (d.activeId (v+1) j (markedMemoryIndependentIncoming hZ d v hv j)) :=
  markedMemoryActiveExchange_remaining _ _ _ _ (markedMemoryIndependentActive_exchange hZ d v hv j)

def markedMemoryIndependentSlotPairs (v : ℕ) (hv : v < n)
    (order : J → Equiv.Perm (Fin pads)) :
    MarkedMemorySlotFamilyFiber (d.activeId v) (d.activeId (v+1))
      (markedMemoryIndependentOutgoing hZ d v hv) (markedMemoryIndependentIncoming hZ d v hv) :=
  fun j => markedMemorySlotFiberOfOrder _ _ _ _ (markedMemoryIndependentActive_remaining hZ d v hv j) (order j)

theorem markedMemoryIndependentSlotPairs_card (v : ℕ) (hv : v < n) :
    Fintype.card (MarkedMemorySlotFamilyFiber (d.activeId v) (d.activeId (v+1))
      (markedMemoryIndependentOutgoing hZ d v hv) (markedMemoryIndependentIncoming hZ d v hv)) =
      pads.factorial ^ Fintype.card J :=
  markedMemorySlotFamilyFiber_card _ _ _ _ (markedMemoryIndependentActive_remaining hZ d v hv)

theorem markedMemoryIndependentQueue_nodup (t : ℕ) (ht : t ≤ 2*n+1) (j : J) :
    (markedMemoryIndependentQueue hZ d t j).Nodup :=
  markedMemoryPendingQueueAt_nodup (d.lifespan j) t ht

theorem markedMemoryIndependentQueue_edge (v : ℕ) (hv : v < n) :
    markedMemoryEdgeQueueAfter (markedMemoryIndependentQueue hZ d (2*v+1))
      (markedMemoryIndependentQueue_nodup hZ d (2*v+1) (by omega))
      (fun j => (d.lifespan j).incoming (2*v+1)) (fun j => (d.lifespan j).outgoing (2*v+1))
      (fun j => decide (2*v+1 < (d.lifespan j).last ((d.lifespan j).outgoing (2*v+1)))) =
      markedMemoryIndependentQueue hZ d (2*(v+1)) := by
  funext j
  rw [markedMemoryEdgeQueueAfter_eq]
  have he : 2*(v+1) = (2*v+1)+1 := by omega
  change _ = markedMemoryPendingQueueAt (d.lifespan j) (2*(v+1))
  rw [he]
  have ho : ¬ (2*v+1) % 2 = 0 := by omega
  simp only [markedMemoryPendingQueueAt, ho, ite_false]
  rfl

end
end ArtinMatthews
