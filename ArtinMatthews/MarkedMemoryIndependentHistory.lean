module

public import ArtinMatthews.MarkedMemoryIndependentEdge


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine chronological history constructed from independent
lifespan/active-run data. The only extra coordinate is one copied-slot
ordering per actual edge and band. The finite assembler receives local
choices already proved to have the independently specified targets. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)

def markedMemoryEdgeTransport {s t : MarkedRawState P (pads+1) B Z} (h : s = t)
    (edge : MarkedMemoryEdgeChoice hZ s) : MarkedMemoryEdgeChoice hZ t := h ▸ edge

theorem markedMemoryEdgeTransport_target {s t : MarkedRawState P (pads+1) B Z} (h : s = t)
    (edge : MarkedMemoryEdgeChoice hZ s) :
    markedMemoryEdgeChoiceTarget hZ t (markedMemoryEdgeTransport hZ h edge) =
      markedMemoryEdgeChoiceTarget hZ s edge := by
  cases h
  rfl

variable {A : J → Type*} [∀ j, DecidableEq (A j)] [∀ j, Fintype (A j)] {n : ℕ}
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (order : Fin n → J → Equiv.Perm (Fin pads))

def markedMemoryIndependentTransitions : MarkedMemoryFiniteTransitions (P := P) (pads := pads) (B := B) hZ n where
  state := markedMemoryIndependentState hZ d
  ghost := markedMemoryIndependentGhost hZ d
  edge := fun v hv => markedMemoryEdgeTransport hZ (markedMemoryIndependentGhost_target hZ d v (Nat.le_of_lt hv)).symm
    (markedMemoryIndependentEdge hZ d v hv (order ⟨v,hv⟩))
  link := by
    intro v hv
    rw [markedMemoryEdgeTransport_target]
    exact markedMemoryIndependentEdge_target hZ d v hv (order ⟨v,hv⟩)

/-- No chronology or history/lifespan bijection is supplied: the history
is assembled from the independently constructed local choices. -/
def markedMemoryIndependentHistory :
    MarkedMemoryChronologicalHistory hZ n (markedMemoryIndependentState hZ d 0 (Nat.zero_le n)) :=
  markedMemoryFiniteTransitions_history hZ (markedMemoryIndependentTransitions hZ d order)

theorem markedMemoryIndependentHistory_target :
    markedMemoryChronologicalTarget hZ (markedMemoryIndependentHistory hZ d order) =
      markedMemoryIndependentPostGhost hZ d n (Nat.le_refl n) :=
  (markedMemoryFiniteTransitions_history_target hZ (markedMemoryIndependentTransitions hZ d order)).trans
    (markedMemoryIndependentGhost_target hZ d n (Nat.le_refl n))

include order in
theorem markedMemoryIndependentHistory_exists :
    ∃ history : MarkedMemoryChronologicalHistory hZ n (markedMemoryIndependentState hZ d 0 (Nat.zero_le n)),
      markedMemoryChronologicalTarget hZ history = markedMemoryIndependentPostGhost hZ d n (Nat.le_refl n) :=
  ⟨markedMemoryIndependentHistory hZ d order, markedMemoryIndependentHistory_target hZ d order⟩

end
end ArtinMatthews
