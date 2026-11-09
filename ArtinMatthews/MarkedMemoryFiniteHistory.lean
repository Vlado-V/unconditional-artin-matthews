module

public import ArtinMatthews.MarkedMemoryFiniteGhost
public import ArtinMatthews.MarkedMemoryFiniteEdge
public import ArtinMatthews.MarkedMemoryTransitionDeterminism
public import ArtinMatthews.MarkedMemoryIndependentHistory


set_option backward.privateInPublic true
@[expose] public section

/-! The actual independent reconstruction factors through the finite
time tableau. Every local choice, order and final ghost is preserved. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)

theorem markedMemoryFinite_edgeTransport_heq {s t : MarkedRawState P (pads+1) B Z}
    (h : s=t) (e : MarkedMemoryEdgeChoice hZ s) :
    HEq (markedMemoryEdgeTransport hZ h e) e := by
  cases h
  rfl

variable {A : J → Type*} [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)] {n : ℕ}
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)

local notation "restored" => markedMemoryFiniteTableau_toIndependent hZ (markedMemoryIndependent_toFinite hZ d)

theorem markedMemoryFinite_restore_history_heq (order : Fin n → J → Equiv.Perm (Fin pads)) :
    HEq (markedMemoryIndependentHistory hZ restored order) (markedMemoryIndependentHistory hZ d order) := by
  apply markedMemoryFiniteTransitions_history_heq_of_vertexChoices hZ
    (markedMemoryIndependentTransitions hZ restored order)
    (markedMemoryFinite_restore_state hZ d 0 (Nat.zero_le n))
    (markedMemoryIndependentHistory hZ d order)
  · intro v
    exact (markedMemoryFiniteTransitions_history_vertexGhost hZ
      (markedMemoryIndependentTransitions hZ d order) v).trans
      (markedMemoryFinite_restore_ghost_heq hZ d v.val (by omega)).symm
  · intro v
    have hOld := markedMemoryFinite_edgeTransport_heq hZ
      (markedMemoryIndependentGhost_target hZ d v.val (Nat.le_of_lt v.2)).symm
      (markedMemoryIndependentEdge hZ d v.val v.2 (order v))
    have hNew := markedMemoryFinite_edgeTransport_heq hZ
      (markedMemoryIndependentGhost_target hZ restored v.val (Nat.le_of_lt v.2)).symm
      (markedMemoryIndependentEdge hZ restored v.val v.2 (order v))
    exact (markedMemoryFiniteTransitions_history_vertexEdge hZ
      (markedMemoryIndependentTransitions hZ d order) v).trans
      (hOld.trans ((markedMemoryFinite_restore_edge_heq hZ d v.val v.2 (order v)).symm.trans hNew.symm))

theorem markedMemoryFinite_restore_history (order : Fin n → J → Equiv.Perm (Fin pads)) :
    markedMemoryHistoryTransport hZ (markedMemoryFinite_restore_state hZ d 0 (Nat.zero_le n))
      (markedMemoryIndependentHistory hZ restored order)=markedMemoryIndependentHistory hZ d order :=
  eq_of_heq ((markedMemoryHistoryTransport_heq hZ (markedMemoryFinite_restore_state hZ d 0 (Nat.zero_le n)) _).trans
    (markedMemoryFinite_restore_history_heq hZ d order))

end
end ArtinMatthews
