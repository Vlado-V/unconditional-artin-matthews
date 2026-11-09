module

public import ArtinMatthews.MarkedMemoryFiniteTableauRecovery
public import ArtinMatthews.MarkedMemoryIndependentEdge


set_option backward.privateInPublic true
@[expose] public section

/-! Canonical time truncation preserves the uniquely determined outgoing
and incoming slots and the retained copied-slot permutation. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)} {n : ℕ}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)

local notation "restored" => markedMemoryFiniteTableau_toIndependent hZ (markedMemoryIndependent_toFinite hZ d)

omit [∀ j,DecidableEq (A j)] in
theorem markedMemoryFinite_restore_outgoingSlot (v : ℕ) (hv : v<n) (j : J) :
    markedMemoryIndependentOutgoing hZ restored v hv j=markedMemoryIndependentOutgoing hZ d v hv j := by
  apply (d.activeId v j).injective
  have h := markedMemoryIndependentOutgoing_eq hZ restored v hv j
  rw [markedMemoryFinite_restore_activeId hZ d v (Nat.le_of_lt hv) j,
    markedMemoryFinite_restore_outgoing hZ d v hv j] at h
  exact h.trans (markedMemoryIndependentOutgoing_eq hZ d v hv j).symm

omit [∀ j,DecidableEq (A j)] in
theorem markedMemoryFinite_restore_incomingSlot (v : ℕ) (hv : v<n) (j : J) :
    markedMemoryIndependentIncoming hZ restored v hv j=markedMemoryIndependentIncoming hZ d v hv j := by
  apply (d.activeId (v+1) j).injective
  have h := markedMemoryIndependentIncoming_eq hZ restored v hv j
  rw [markedMemoryFinite_restore_activeId hZ d (v+1) (by omega) j,
    markedMemoryFinite_restore_incoming hZ d v hv j] at h
  exact h.trans (markedMemoryIndependentIncoming_eq hZ d v hv j).symm

theorem markedMemoryFinite_restore_slotPair (v : ℕ) (hv : v<n)
    (order : J → Equiv.Perm (Fin pads)) (j : J) :
    (markedMemoryIndependentSlotPairs hZ restored v hv order j).1 =
      (markedMemoryIndependentSlotPairs hZ d v hv order j).1 := by
  have hs : (restored).activeId v=d.activeId v := funext
    (markedMemoryFinite_restore_activeId hZ d v (Nat.le_of_lt hv))
  have ht : (restored).activeId (v+1)=d.activeId (v+1) := funext
    (markedMemoryFinite_restore_activeId hZ d (v+1) (by omega))
  have ho : markedMemoryIndependentOutgoing hZ restored v hv=markedMemoryIndependentOutgoing hZ d v hv :=
    funext (markedMemoryFinite_restore_outgoingSlot hZ d v hv)
  have hi : markedMemoryIndependentIncoming hZ restored v hv=markedMemoryIndependentIncoming hZ d v hv :=
    funext (markedMemoryFinite_restore_incomingSlot hZ d v hv)
  dsimp only [markedMemoryIndependentSlotPairs,markedMemorySlotFiberOfOrder]
  simp only [hs,ht,ho,hi]

theorem markedMemoryFinite_restore_sourceSlots (v : ℕ) (hv : v<n)
    (order : J → Equiv.Perm (Fin pads)) :
    markedMemoryIndependentSourceSlots hZ restored v hv order=markedMemoryIndependentSourceSlots hZ d v hv order := by
  funext j
  exact congrArg Prod.fst (markedMemoryFinite_restore_slotPair hZ d v hv order j)

theorem markedMemoryFinite_restore_targetSlots (v : ℕ) (hv : v<n)
    (order : J → Equiv.Perm (Fin pads)) :
    markedMemoryIndependentTargetSlots hZ restored v hv order=markedMemoryIndependentTargetSlots hZ d v hv order := by
  funext j
  exact congrArg Prod.snd (markedMemoryFinite_restore_slotPair hZ d v hv order j)

theorem markedMemoryFinite_restore_slottedActive (v : ℕ) (hv : v<n)
    (order : J → Equiv.Perm (Fin pads)) :
    markedMemoryIndependentSlottedActive hZ restored v hv order=markedMemoryIndependentSlottedActive hZ d v hv order := by
  funext j k
  unfold markedMemoryIndependentSlottedActive
  rw [markedMemoryFinite_restore_particle,markedMemoryFinite_restore_activeId hZ d v (Nat.le_of_lt hv) j,
    markedMemoryFinite_restore_sourceSlots]

end
end ArtinMatthews
