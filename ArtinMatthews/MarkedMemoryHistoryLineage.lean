module

public import ArtinMatthews.MarkedMemoryHistoryGhostOrigins
public import ArtinMatthews.MarkedMemoryHistoryEdgeSlotOrigins
public import ArtinMatthews.MarkedMemoryHistoryOriginComposition
public import ArtinMatthews.MarkedMemoryHistoryBirths


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine recursive lineage of the actual final indexed population.
Every surviving particle comes from one initial index or one actually
performed birth, without identifying equal numeric prime values. -/
namespace ArtinMatthews
noncomputable section

def markedMemoryHistoryTerminalOrigin {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) :
    {n : ℕ} → {s : MarkedRawState P (pads+1) B Z} →
      (history : MarkedMemoryChronologicalHistory hZ n s) →
      MarkedMemoryPopulationIndex (markedMemoryChronologicalTarget hZ history) ↪
        (MarkedMemoryPopulationIndex s ⊕ MarkedMemoryHistoryBirths hZ history)
  | 0,s,ghost => markedMemoryGhostPopulationOrigin hZ s ghost
  | _+1,s,history =>
      markedMemoryOriginCompose
        (markedMemoryOriginCompose (markedMemoryHistoryTerminalOrigin hZ history.2.2)
          (markedMemoryEdgeSlotPopulationOrigin hZ
            (markedMemoryGhostChoiceTarget hZ s history.1) history.2.1))
        (markedMemoryGhostPopulationOrigin hZ s history.1)

/-- The actual terminal lineage preserves the literal prime label. -/
theorem markedMemoryHistoryTerminalOrigin_prime {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {n : ℕ}
    {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s)
    (i : MarkedMemoryPopulationIndex (markedMemoryChronologicalTarget hZ history)) :
    Sum.elim (markedMemoryPopulationPrime s) (markedMemoryHistoryBirthPrime hZ history)
      (markedMemoryHistoryTerminalOrigin hZ history i) =
        markedMemoryPopulationPrime (markedMemoryChronologicalTarget hZ history) i := by
  induction n generalizing s with
  | zero => exact markedMemoryGhostPopulationOrigin_prime hZ s history i
  | succ n ih =>
    exact markedMemoryOriginCompose_mark _ _ _ _ _ _ _
      (markedMemoryOriginCompose_mark _ _ _ _ _ _ _
        (ih history.2.2) (markedMemoryEdgeSlotPopulationOrigin_prime hZ _ history.2.1))
      (markedMemoryGhostPopulationOrigin_prime hZ s history.1) i

/-- Distinct final indexed particles always have distinct origin identities,
independently of the separate global distinctness condition on numeric marks. -/
theorem markedMemoryHistoryTerminalOrigin_injective {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) :
    Function.Injective (markedMemoryHistoryTerminalOrigin hZ history) :=
  (markedMemoryHistoryTerminalOrigin hZ history).injective

end
end ArtinMatthews
