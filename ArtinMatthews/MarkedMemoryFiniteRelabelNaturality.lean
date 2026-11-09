module

public import ArtinMatthews.MarkedMemoryFiniteRecoveryExt
public import ArtinMatthews.MarkedMemoryFiniteSlots
public import ArtinMatthews.MarkedMemoryIndependentRelabel


set_option backward.privateInPublic true
@[expose] public section

/-! Finite restriction commutes with genuine identity relabeling, and
finite data equality determines the actual copied-slot permutations. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {A A' A'' : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  [∀ j,Fintype (A' j)] [∀ j,DecidableEq (A' j)]
  [∀ j,Fintype (A'' j)] [∀ j,DecidableEq (A'' j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)

theorem markedMemoryFinite_restore_relabel (e : (j : J) → A j ≃ A' j) :
    markedMemoryIndependent_toFinite hZ (markedMemoryIndependentRelabel hZ e
        (markedMemoryFiniteTableau_toIndependent hZ (markedMemoryIndependent_toFinite hZ d)))=
      markedMemoryIndependent_toFinite hZ (markedMemoryIndependentRelabel hZ e d) := by
  apply markedMemoryFinite_recovery_ext hZ
  · intro j a; rfl
  · intro j a; rfl
  · intro t ht j a
    exact markedMemoryFinite_restore_active hZ d t ht j ((e j).symm a)
  · intro v hv
    exact markedMemoryFinite_restore_position hZ d v hv
  · intro v hv j
    apply Function.Embedding.ext
    intro k
    change e j ((markedMemoryFiniteTableau_toIndependent hZ (markedMemoryIndependent_toFinite hZ d)).activeId v j k)=
      e j (d.activeId v j k)
    rw [markedMemoryFinite_restore_activeId hZ d v hv j]
  · rfl
  · intro t ht j
    rw [markedMemoryIndependentRelabel_queue,markedMemoryIndependentRelabel_queue,
      markedMemoryFinite_restore_queue hZ d t ht j]

theorem markedMemoryFinite_relabel_trans (e : (j : J) → A j ≃ A' j) (f : (j : J) → A' j ≃ A'' j) :
    markedMemoryIndependent_toFinite hZ (markedMemoryIndependentRelabel hZ f (markedMemoryIndependentRelabel hZ e d))=
      markedMemoryIndependent_toFinite hZ (markedMemoryIndependentRelabel hZ (fun j => (e j).trans (f j)) d) := by
  apply markedMemoryFinite_recovery_ext hZ
  · intro j a; rfl
  · intro j a; rfl
  · intro t _ j a; rfl
  · intro v _; rfl
  · intro v _ j
    apply Function.Embedding.ext
    intro k
    rfl
  · rfl
  · intro t _ j
    rw [markedMemoryIndependentRelabel_queue,markedMemoryIndependentRelabel_queue,markedMemoryIndependentRelabel_queue]
    simp only [List.map_map,Function.comp_def]
    rfl

theorem markedMemoryFinite_eq_sourceSlots
    (f : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
    (h : markedMemoryIndependent_toFinite hZ d=markedMemoryIndependent_toFinite hZ f)
    (v : ℕ) (hv : v<n) (order : J → Equiv.Perm (Fin pads)) :
    markedMemoryIndependentSourceSlots hZ d v hv order=markedMemoryIndependentSourceSlots hZ f v hv order := by
  have hr := congrArg (markedMemoryFiniteTableau_toIndependent hZ) h
  exact (markedMemoryFinite_restore_sourceSlots hZ d v hv order).symm.trans
    ((congrArg (fun x : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n =>
        markedMemoryIndependentSourceSlots hZ x v hv order) hr).trans
      (markedMemoryFinite_restore_sourceSlots hZ f v hv order))

end
end ArtinMatthews
