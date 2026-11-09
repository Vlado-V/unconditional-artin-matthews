module

public import ArtinMatthews.MarkedMemoryIndependentRelabelEdge
public import ArtinMatthews.MarkedMemoryTransitionDeterminism


set_option backward.privateInPublic true
@[expose] public section

/-! Relabeling independent identities preserves the entire reconstructed
chronological history, for the same copied-slot orders. The equality is
proved from literal local choices and the deterministic assembler. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {A A' : J → Type*}
  [∀ j, DecidableEq (A j)] [∀ j, Fintype (A j)]
  [∀ j, DecidableEq (A' j)] [∀ j, Fintype (A' j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (e : (j : J) → A j ≃ A' j)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)

theorem markedMemoryRelabelEdgeTransport_heq
    {s t : MarkedRawState P (pads+1) B Z} (h : s = t) (edge : MarkedMemoryEdgeChoice hZ s) :
    HEq (markedMemoryEdgeTransport hZ h edge) edge := by
  cases h
  rfl

theorem markedMemoryIndependentRelabel_history_heq (order : Fin n → J → Equiv.Perm (Fin pads)) :
    HEq (markedMemoryIndependentHistory hZ (markedMemoryIndependentRelabel hZ e d) order)
      (markedMemoryIndependentHistory hZ d order) := by
  apply markedMemoryChronologicalHistory_hext hZ
    (markedMemoryIndependentRelabel_state hZ e d 0 (Nat.zero_le n))
  · intro v
    exact (markedMemoryFiniteTransitions_history_vertexGhost hZ
      (markedMemoryIndependentTransitions hZ (markedMemoryIndependentRelabel hZ e d) order) v).trans
      ((markedMemoryIndependentRelabel_ghost_heq hZ e d v.val (by omega)).trans
        (markedMemoryFiniteTransitions_history_vertexGhost hZ
          (markedMemoryIndependentTransitions hZ d order) v).symm)
  · intro v
    have hn := markedMemoryRelabelEdgeTransport_heq hZ
      (markedMemoryIndependentGhost_target hZ (markedMemoryIndependentRelabel hZ e d) v.val (Nat.le_of_lt v.2)).symm
      (markedMemoryIndependentEdge hZ (markedMemoryIndependentRelabel hZ e d) v.val v.2 (order v))
    have ho := markedMemoryRelabelEdgeTransport_heq hZ
      (markedMemoryIndependentGhost_target hZ d v.val (Nat.le_of_lt v.2)).symm
      (markedMemoryIndependentEdge hZ d v.val v.2 (order v))
    exact (markedMemoryFiniteTransitions_history_vertexEdge hZ
      (markedMemoryIndependentTransitions hZ (markedMemoryIndependentRelabel hZ e d) order) v).trans
      (hn.trans ((markedMemoryIndependentRelabel_edge_heq hZ e d v.val v.2 (order v)).trans
        (ho.symm.trans (markedMemoryFiniteTransitions_history_vertexEdge hZ
          (markedMemoryIndependentTransitions hZ d order) v).symm)))

theorem markedMemoryIndependentRelabel_history (order : Fin n → J → Equiv.Perm (Fin pads)) :
    markedMemoryHistoryTransport hZ (markedMemoryIndependentRelabel_state hZ e d 0 (Nat.zero_le n))
      (markedMemoryIndependentHistory hZ (markedMemoryIndependentRelabel hZ e d) order) =
        markedMemoryIndependentHistory hZ d order :=
  eq_of_heq ((markedMemoryHistoryTransport_heq hZ
    (markedMemoryIndependentRelabel_state hZ e d 0 (Nat.zero_le n)) _).trans
    (markedMemoryIndependentRelabel_history_heq hZ e d order))

omit e [∀ j, DecidableEq (A' j)] [∀ j, Fintype (A' j)] in
theorem markedMemoryIndependentRelabelFin_history_heq (order : Fin n → J → Equiv.Perm (Fin pads)) :
    HEq (markedMemoryIndependentHistory hZ (markedMemoryIndependentRelabelFin hZ d) order)
      (markedMemoryIndependentHistory hZ d order) :=
  markedMemoryIndependentRelabel_history_heq hZ (fun j => Fintype.equivFin (A j)) d order

end
end ArtinMatthews
