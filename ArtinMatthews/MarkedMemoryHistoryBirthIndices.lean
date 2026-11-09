module

public import ArtinMatthews.MarkedMemoryHistoryGhostChoice
public import ArtinMatthews.MarkedMemoryHistoryEdgeChoice


set_option backward.privateInPublic true
@[expose] public section

/-! Actual indexed ghost and fresh-edge birth occurrences. -/
namespace ArtinMatthews

abbrev MarkedMemoryGhostBirthIndex {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    {hZ : ∀ z ∈ Z, IsCoprime z.1 z.2} {s : MarkedRawState P M B Z}
    (choice : MarkedMemoryGhostChoice hZ s) := Σ j : J, Fin (choice.sizes.1 j : ℕ)

def markedMemoryGhostBirthPrime {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    {hZ : ∀ z ∈ Z, IsCoprime z.1 z.2} {s : MarkedRawState P M B Z}
    (choice : MarkedMemoryGhostChoice hZ s) (birth : MarkedMemoryGhostBirthIndex choice) : Nat.Primes :=
  (choice.births birth.1 birth.2).1

/-- Promoted groups have no performed fresh birth address. -/
abbrev MarkedMemoryEdgeBirthIndex {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    {hZ : ∀ z ∈ Z, IsCoprime z.1 z.2} {s : MarkedRawState P (pads+1) B Z}
    (choice : MarkedMemoryEdgeChoice hZ s) := {j : J // choice.2.1.promotions j=none}

def markedMemoryEdgeBirthPrime {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    {hZ : ∀ z ∈ Z, IsCoprime z.1 z.2} {s : MarkedRawState P (pads+1) B Z}
    (choice : MarkedMemoryEdgeChoice hZ s) (birth : MarkedMemoryEdgeBirthIndex choice) : Nat.Primes :=
  (markedRawEdgeTargetLast (markedRawSlotEquiv choice.1 s).2.2
    choice.2.1.promotions choice.2.1.fresh birth.1).1


end ArtinMatthews
