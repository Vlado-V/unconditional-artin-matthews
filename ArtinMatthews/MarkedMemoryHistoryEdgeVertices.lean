module

public import ArtinMatthews.MarkedMemoryHistoryEdgeProduct


set_option backward.privateInPublic true
@[expose] public section

/-! The exact raw edge product is the finite product over the literal
chronological edge accessors. This exposes every copied-slot decoration
without replacing any local coefficient or test. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)

def markedMemoryRawEdgeValue (χ : MarkedRawState P (pads+1) B Z → ℂ)
    {s : MarkedRawState P (pads+1) B Z} (edge : MarkedMemoryEdgeChoice hZ s) : ℂ :=
  markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q 1 χ (markedRawSlotEquiv edge.1 s) edge.2.1

theorem markedMemoryRawEdgeValue_heq (χ : MarkedRawState P (pads+1) B Z → ℂ)
    {s t : MarkedRawState P (pads+1) B Z} (hs : s=t)
    (a : MarkedMemoryEdgeChoice hZ s) (b : MarkedMemoryEdgeChoice hZ t) (hab : HEq a b) :
    markedMemoryRawEdgeValue hZ ψ η d₀ Y Q χ a = markedMemoryRawEdgeValue hZ ψ η d₀ Y Q χ b := by
  cases hs
  have he : a=b := eq_of_heq hab
  cases he
  rfl

theorem markedMemoryHistoryRawEdgeProduct_vertices
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) (n offset : ℕ)
    {s : MarkedRawState P (pads+1) B Z} (H : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryHistoryRawEdgeProduct hZ ψ η d₀ Y Q χ n offset H =
      ∏ v : Fin n,markedMemoryRawEdgeValue hZ ψ η d₀ Y Q (χ (offset+v.val))
        (markedMemoryHistoryVertexEdge hZ H v) := by
  induction n generalizing s offset with
  | zero => simp [markedMemoryHistoryRawEdgeProduct]
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    change markedMemoryRawEdgeValue hZ ψ η d₀ Y Q (χ offset) H.2.1 *
      markedMemoryHistoryRawEdgeProduct hZ ψ η d₀ Y Q χ n (offset+1) H.2.2 =
      markedMemoryRawEdgeValue hZ ψ η d₀ Y Q (χ offset) H.2.1 *
        ∏ v : Fin n,markedMemoryRawEdgeValue hZ ψ η d₀ Y Q (χ (offset+(v.val+1)))
          (markedMemoryHistoryVertexEdge hZ H.2.2 v)
    rw [ih]
    congr 1
    apply Finset.prod_congr rfl
    intro v _
    rw [show (offset+1)+v.val=offset+(v.val+1) by omega]

end
end ArtinMatthews
