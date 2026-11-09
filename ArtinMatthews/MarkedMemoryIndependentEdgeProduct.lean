module

public import ArtinMatthews.MarkedMemoryHistoryEdgeVertices


set_option backward.privateInPublic true
@[expose] public section

/-! The literal independent edge choices give the vertexwise raw joint
kernel at their actual source and target slot permutations. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)

theorem markedMemoryRawEdgeValue_transport (χ : MarkedRawState P (pads+1) B Z → ℂ)
    {s t : MarkedRawState P (pads+1) B Z} (h : s=t) (edge : MarkedMemoryEdgeChoice hZ s) :
    markedMemoryRawEdgeValue hZ ψ η d₀ Y Q χ (markedMemoryEdgeTransport hZ h edge) =
      markedMemoryRawEdgeValue hZ ψ η d₀ Y Q χ edge := by
  cases h
  rfl

variable {A : J → Type*} [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (order : Fin n → J → Equiv.Perm (Fin pads))

theorem markedMemoryIndependent_rawEdgeProduct
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) (offset : ℕ) :
    markedMemoryHistoryRawEdgeProduct hZ ψ η d₀ Y Q χ n offset (markedMemoryIndependentHistory hZ d order) =
      ∏ v : Fin n,markedMemoryRawEdgeValue hZ ψ η d₀ Y Q (χ (offset+v.val))
        (markedMemoryIndependentEdge hZ d v.val v.2 (order v)) := by
  rw [markedMemoryHistoryRawEdgeProduct_vertices]
  apply Finset.prod_congr rfl
  intro v _
  have he := markedMemoryRawEdgeValue_heq hZ ψ η d₀ Y Q (χ (offset+v.val))
    (markedMemoryIndependent_vertex_edge_source hZ d order v) _ _
    (markedMemoryFiniteTransitions_history_vertexEdge hZ (markedMemoryIndependentTransitions hZ d order) v)
  exact he.trans (markedMemoryRawEdgeValue_transport hZ ψ η d₀ Y Q _ _ _)

theorem markedMemoryIndependentRawEdge_joint (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (v : ℕ) (hv : v < n) (ord : J → Equiv.Perm (Fin pads)) :
    markedMemoryRawEdgeValue hZ ψ η d₀ Y Q χ (markedMemoryIndependentEdge hZ d v hv ord) =
    markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q 1 χ
      (markedRawSlotEquiv (markedMemoryIndependentSourceSlots hZ d v hv ord)
        (markedMemoryIndependentPostGhost hZ d v (Nat.le_of_lt hv)))
      ((markedRawSlotEquiv (markedMemoryIndependentTargetSlots hZ d v hv ord)).symm
        (markedMemoryIndependentState hZ d (v+1) hv)) := by
  change markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q 1 χ
    (markedRawSlotEquiv (markedMemoryIndependentSourceSlots hZ d v hv ord)
      (markedMemoryIndependentPostGhost hZ d v (Nat.le_of_lt hv)))
    (markedMemoryIndependentRawEdge hZ d v hv ord) = _
  rw [markedRawEdgeChoiceCoefficient_eq_joint,markedMemoryIndependentRawEdge_target]
  rfl

end
end ArtinMatthews
