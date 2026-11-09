module

public import ArtinMatthews.MarkedMemoryHistorySlotOrigins
public import ArtinMatthews.MarkedMemoryHistoryEdgeOriginsPrime
public import ArtinMatthews.MarkedMemoryHistoryBirthIndices


set_option backward.privateInPublic true
@[expose] public section

/-! The literal origin injection for an edge with both endpoint slot
permutations. Stores and promotions retain identities; only actually fresh
edge labels receive birth addresses. -/
namespace ArtinMatthews
noncomputable section

def markedMemoryEdgeSlotPopulationOrigin {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedMemoryEdgeChoice hZ s) :
    MarkedMemoryPopulationIndex (markedMemoryEdgeChoiceTarget hZ s choice) ↪
      (MarkedMemoryPopulationIndex s ⊕ MarkedMemoryEdgeBirthIndex choice) :=
  (markedMemorySlotPopulationEquiv choice.2.2
    (markedRawEdgeTargetState hZ (markedRawSlotEquiv choice.1 s) choice.2.1)).toEmbedding.trans
    ((markedMemoryEdgePopulationOrigin hZ (markedRawSlotEquiv choice.1 s) choice.2.1).trans
      (Function.Embedding.sumMap (markedMemorySlotPopulationEquiv choice.1 s).toEmbedding
        (Function.Embedding.refl _)))

/-- Both slot permutations transport the same numeric prime along the
actual indexed origin. No numeric distinctness is used. -/
theorem markedMemoryEdgeSlotPopulationOrigin_prime {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedMemoryEdgeChoice hZ s)
    (i : MarkedMemoryPopulationIndex (markedMemoryEdgeChoiceTarget hZ s choice)) :
    Sum.elim (markedMemoryPopulationPrime s) (markedMemoryEdgeBirthPrime choice)
        (markedMemoryEdgeSlotPopulationOrigin hZ s choice i) =
      markedMemoryPopulationPrime (markedMemoryEdgeChoiceTarget hZ s choice) i := by
  let i₀ := markedMemorySlotPopulationEquiv choice.2.2
    (markedRawEdgeTargetState hZ (markedRawSlotEquiv choice.1 s) choice.2.1) i
  have h := markedMemoryEdgePopulationOrigin_prime hZ (markedRawSlotEquiv choice.1 s) choice.2.1 i₀
  have ht := markedMemorySlotPopulationEquiv_prime choice.2.2
    (markedRawEdgeTargetState hZ (markedRawSlotEquiv choice.1 s) choice.2.1) i
  change Sum.elim (markedMemoryPopulationPrime s) (markedMemoryEdgeBirthPrime choice)
      (Sum.map (markedMemorySlotPopulationEquiv choice.1 s) id
        (markedMemoryEdgePopulationOrigin hZ (markedRawSlotEquiv choice.1 s) choice.2.1 i₀)) = _
  generalize ho : markedMemoryEdgePopulationOrigin hZ (markedRawSlotEquiv choice.1 s) choice.2.1 i₀ = o at h ⊢
  cases o with
  | inl old =>
    simp only [Sum.map_inl, Sum.elim_inl] at h ⊢
    exact (markedMemorySlotPopulationEquiv_prime choice.1 s old).trans (h.trans ht)
  | inr birth =>
    simp only [Sum.map_inr, Sum.elim_inr, id_eq]
    exact h.trans ht

end
end ArtinMatthews
