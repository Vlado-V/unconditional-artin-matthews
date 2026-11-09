module

public import ArtinMatthews.MarkedMemoryIndependentRelabelHistory
public import ArtinMatthews.MarkedMemoryFiniteHistory


set_option backward.privateInPublic true
@[expose] public section

/-! Canonical finite-label tableaux are obtained by the proved per-band
equivalences to Fin(card A), followed by the genuine finite-time wrapper.
Their reconstructed raw states and histories remain the original ones. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j, DecidableEq (A j)] [∀ j, Fintype (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)

def markedMemoryIndependentCanonicalFinite :
    MarkedMemoryFiniteTableau (A := fun j => Fin (Fintype.card (A j)))
      (P := P) (pads := pads) (B := B) hZ n :=
  markedMemoryIndependent_toFinite hZ (markedMemoryIndependentRelabelFin hZ d)

theorem markedMemoryIndependentCanonicalFinite_state (v : ℕ) (hv : v ≤ n) :
    markedMemoryIndependentState hZ
      (markedMemoryFiniteTableau_toIndependent hZ (markedMemoryIndependentCanonicalFinite hZ d)) v hv =
      markedMemoryIndependentState hZ d v hv :=
  (markedMemoryFinite_restore_state hZ (markedMemoryIndependentRelabelFin hZ d) v hv).trans
    (markedMemoryIndependentRelabel_state hZ (fun j => Fintype.equivFin (A j)) d v hv)

theorem markedMemoryIndependentCanonicalFinite_history_heq
    (order : Fin n → J → Equiv.Perm (Fin pads)) :
    HEq (markedMemoryIndependentHistory hZ
      (markedMemoryFiniteTableau_toIndependent hZ (markedMemoryIndependentCanonicalFinite hZ d)) order)
      (markedMemoryIndependentHistory hZ d order) :=
  (markedMemoryFinite_restore_history_heq hZ (markedMemoryIndependentRelabelFin hZ d) order).trans
    (markedMemoryIndependentRelabelFin_history_heq hZ d order)

theorem markedMemoryIndependentCanonicalFinite_history
    (order : Fin n → J → Equiv.Perm (Fin pads)) :
    markedMemoryHistoryTransport hZ (markedMemoryIndependentCanonicalFinite_state hZ d 0 (Nat.zero_le n))
      (markedMemoryIndependentHistory hZ
        (markedMemoryFiniteTableau_toIndependent hZ (markedMemoryIndependentCanonicalFinite hZ d)) order) =
      markedMemoryIndependentHistory hZ d order :=
  eq_of_heq ((markedMemoryHistoryTransport_heq hZ
    (markedMemoryIndependentCanonicalFinite_state hZ d 0 (Nat.zero_le n)) _).trans
    (markedMemoryIndependentCanonicalFinite_history_heq hZ d order))

end
end ArtinMatthews
