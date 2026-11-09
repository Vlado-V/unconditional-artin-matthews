module

public import ArtinMatthews.MarkedMemoryEdgeOriginLabels
public import ArtinMatthews.MarkedMemoryHistoryEdgeSlotOrigins


set_option backward.privateInPublic true
@[expose] public section

/-! Identity-label compatibility with both actual endpoint slot
permutations. The raw edge rule is transported through the two genuine
population equivalences, with no symmetry assumption on labels. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {A : J → Type*} {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
  (choice : MarkedMemoryEdgeChoice hZ s)
  (activeId : (j : J) → Fin (pads+1) → A j)
  (pendingId : (j : J) → Fin (s.2.2.1.1 j : ℕ) → A j) (incoming : (j : J) → A j)

theorem markedMemoryEdgeSlotPopulationOrigin_label
    (hprom : ∀ j k, choice.2.1.promotions j = some k → pendingId j k = incoming j)
    (i : MarkedMemoryPopulationIndex (markedMemoryEdgeChoiceTarget hZ s choice)) :
    Sum.elim (markedMemoryEdgeSourceLabel s activeId pendingId)
      (markedMemoryEdgeFreshLabel hZ (markedRawSlotEquiv choice.1 s) choice.2.1 incoming)
      (markedMemoryEdgeSlotPopulationOrigin hZ s choice i) =
        markedMemoryEdgeTargetLabel hZ (markedRawSlotEquiv choice.1 s) choice.2.1
          (fun j k => activeId j (choice.1 j k)) pendingId incoming
          (markedMemorySlotPopulationEquiv choice.2.2
            (markedRawEdgeTargetState hZ (markedRawSlotEquiv choice.1 s) choice.2.1) i) := by
  let i₀ := markedMemorySlotPopulationEquiv choice.2.2
    (markedRawEdgeTargetState hZ (markedRawSlotEquiv choice.1 s) choice.2.1) i
  have h := markedMemoryEdgePopulationOrigin_label hZ (markedRawSlotEquiv choice.1 s) choice.2.1
    (fun j k => activeId j (choice.1 j k)) pendingId incoming hprom i₀
  change Sum.elim (markedMemoryEdgeSourceLabel s activeId pendingId)
    (markedMemoryEdgeFreshLabel hZ (markedRawSlotEquiv choice.1 s) choice.2.1 incoming)
    (Sum.map (markedMemorySlotPopulationEquiv choice.1 s) id
      (markedMemoryEdgePopulationOrigin hZ (markedRawSlotEquiv choice.1 s) choice.2.1 i₀)) = _
  generalize ho : markedMemoryEdgePopulationOrigin hZ (markedRawSlotEquiv choice.1 s) choice.2.1 i₀ = o at h ⊢
  cases o with
  | inl old =>
    exact (markedMemoryEdgeSourceLabel_slots s activeId pendingId choice.1 old).trans h
  | inr birth => exact h

end
end ArtinMatthews
