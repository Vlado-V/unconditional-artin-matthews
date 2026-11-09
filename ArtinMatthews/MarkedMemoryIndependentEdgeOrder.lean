module

public import ArtinMatthews.MarkedMemoryIndependentEdgeProduct
public import ArtinMatthews.MarkedMemoryPhysicalCoreMemory


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine position-only physical edge kernel is independent of
common-survivor slot order. This is proved from the actual joint kernel
and the fixed outgoing/incoming identity slots. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)

theorem markedMemoryIndependentRawEdge_position_order (F : Z → ℂ)
    (v : ℕ) (hv : v < n) (left right : J → Equiv.Perm (Fin pads)) :
    markedMemoryRawEdgeValue hZ ψ η d₀ Y Q (fun s => F s.1) (markedMemoryIndependentEdge hZ d v hv left) =
      markedMemoryRawEdgeValue hZ ψ η d₀ Y Q (fun s => F s.1) (markedMemoryIndependentEdge hZ d v hv right) := by
  rw [markedMemoryIndependentRawEdge_joint,markedMemoryIndependentRawEdge_joint]
  apply markedRawEdgeJointCoefficient_slots_positionMemory hZ ψ η d₀ Y Q 1 (fun z _ => F z)
  · intro j
    change markedMemorySlotFamilySource _ _ _ _ (markedMemoryIndependentSlotPairs hZ d v hv left) j (Fin.last pads) =
      markedMemorySlotFamilySource _ _ _ _ (markedMemoryIndependentSlotPairs hZ d v hv right) j (Fin.last pads)
    rw [markedMemorySlotFamilySource_last,markedMemorySlotFamilySource_last]
  · intro j
    change markedMemorySlotFamilyTargetInverse _ _ _ _ (markedMemoryIndependentSlotPairs hZ d v hv left) j (Fin.last pads) =
      markedMemorySlotFamilyTargetInverse _ _ _ _ (markedMemoryIndependentSlotPairs hZ d v hv right) j (Fin.last pads)
    rw [markedMemorySlotFamilyTargetInverse_last,markedMemorySlotFamilyTargetInverse_last]

theorem markedMemoryIndependentRawProduct_position_order (F : ℕ → Z → ℂ)
    (left right : Fin n → J → Equiv.Perm (Fin pads)) (offset : ℕ) :
    markedMemoryHistoryRawEdgeProduct hZ ψ η d₀ Y Q (fun t s => F t s.1) n offset
      (markedMemoryIndependentHistory hZ d left) =
    markedMemoryHistoryRawEdgeProduct hZ ψ η d₀ Y Q (fun t s => F t s.1) n offset
      (markedMemoryIndependentHistory hZ d right) := by
  rw [markedMemoryIndependent_rawEdgeProduct,markedMemoryIndependent_rawEdgeProduct]
  exact Finset.prod_congr rfl (fun v _ =>
    markedMemoryIndependentRawEdge_position_order hZ d ψ η d₀ Y Q (F (offset+v.val)) v.val v.2 _ _)

end
end ArtinMatthews
