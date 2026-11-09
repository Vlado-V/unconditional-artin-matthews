module

public import ArtinMatthews.MarkedMemoryIndependentPopulation


set_option backward.privateInPublic true
@[expose] public section

/-! The independent identity labels retain the literal numeric prime
at every constructed population index. Repeated prime values remain
permitted; no injection of this mark map is required. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j, DecidableEq (A j)] [∀ j, Fintype (A j)]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {n : ℕ}
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)

def markedMemoryIndependentPrime (a : Σ j, A j) : Nat.Primes := (d.particle a.1 a.2).1.1

theorem markedMemoryIndependentPopulationLabel_prime (t : ℕ) (ht : t ≤ 2*n+1)
    (i : MarkedMemoryPopulationIndex (markedMemoryIndependentStageState hZ d t ht)) :
    markedMemoryIndependentPrime hZ d (markedMemoryIndependentPopulationLabel hZ d t ht i) =
      markedMemoryPopulationPrime (markedMemoryIndependentStageState hZ d t ht) i := by
  rcases i with ⟨j,k⟩ | ⟨j,k⟩ <;> rfl

end
end ArtinMatthews
