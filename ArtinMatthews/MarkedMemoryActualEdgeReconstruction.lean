module

public import ArtinMatthews.MarkedMemoryActualEdgeReconstructionFields
public import ArtinMatthews.MarkedMemoryChoiceExt


set_option backward.privateInPublic true
@[expose] public section

/-! Recover the complete original slotted edge from the extracted actual
tableau and its recovered copied-slot order. Every raw choice field and
both endpoint permutations are retained. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s)
  (ha : MarkedMemoryHistoryAnchorAdmissible hZ history) (v : Fin n)

theorem markedMemoryActualTableau_edge_heq :
    HEq (markedMemoryIndependentEdge hZ (markedMemoryActualTableau hZ history ha)
      v.val v.2 (markedMemoryActualOrder hZ history ha v))
      (markedMemoryHistoryVertexEdge hZ history v) :=
  markedMemoryEdgeChoice_heq_of_fields hZ (markedMemoryActualTableau_edgeSource hZ history ha v)
    _ _ (markedMemoryActualOrder_sourceSlots hZ history ha v)
    (markedMemoryActualRawEdge_heq hZ history ha v)
    (markedMemoryActualOrder_targetSlots hZ history ha v)

end
end ArtinMatthews
