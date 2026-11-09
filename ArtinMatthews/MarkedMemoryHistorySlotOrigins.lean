module

public import ArtinMatthews.MarkedMemoryHistoryEdgeOriginsPopulation
public import ArtinMatthews.MarkedMinorArcRawSlotAverage


set_option backward.privateInPublic true
@[expose] public section

/-! Actual population identities through slot symmetrization. Active slot
indices are permuted; every pending identity remains fixed. -/
namespace ArtinMatthews

def markedMemorySlotPopulationEquiv {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (σ : J → Equiv.Perm (Fin M)) (s : MarkedRawState P M B Z) :
    MarkedMemoryPopulationIndex (markedRawSlotEquiv σ s) ≃ MarkedMemoryPopulationIndex s :=
  Equiv.sumCongr (Equiv.sigmaCongrRight (fun j => σ j)) (Equiv.refl _)

@[simp] theorem markedMemorySlotPopulationEquiv_active {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (σ : J → Equiv.Perm (Fin M)) (s : MarkedRawState P M B Z) (j : J) (i : Fin M) :
    markedMemorySlotPopulationEquiv σ s (Sum.inl ⟨j,i⟩)=Sum.inl ⟨j,σ j i⟩ := rfl

@[simp] theorem markedMemorySlotPopulationEquiv_pending {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (σ : J → Equiv.Perm (Fin M)) (s : MarkedRawState P M B Z)
    (j : J) (i : Fin (s.2.2.1.1 j : ℕ)) :
    markedMemorySlotPopulationEquiv σ s (Sum.inr ⟨j,i⟩)=Sum.inr ⟨j,i⟩ := rfl

/-- Numeric marks follow their indexed permutation, with repeated values
allowed and no change to pending particle order. -/
theorem markedMemorySlotPopulationEquiv_prime {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (σ : J → Equiv.Perm (Fin M)) (s : MarkedRawState P M B Z)
    (i : MarkedMemoryPopulationIndex (markedRawSlotEquiv σ s)) :
    markedMemoryPopulationPrime s (markedMemorySlotPopulationEquiv σ s i)=
      markedMemoryPopulationPrime (markedRawSlotEquiv σ s) i := by
  rcases i with ⟨j,i⟩ | ⟨j,i⟩ <;> rfl

end ArtinMatthews
