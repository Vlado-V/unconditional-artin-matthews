module

public import ArtinMatthews.MarkedMemoryPotentialBirths


set_option backward.privateInPublic true
@[expose] public section

/-! Exact product of local birth multipliers along a literal history.
The closed product keeps the chronological ghost and edge visit indices,
including every unperformed potential address. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators

def markedMemoryGhostLocalBirthProduct
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    {hZ : ∀ z ∈ Z, IsCoprime z.1 z.2}
    (U : ℕ → J → Fin B → Option Nat.Primes → ℂ) (j : ℕ)
    {s : MarkedRawState P M B Z} (c : MarkedMemoryGhostChoice hZ s) : ℂ :=
  ∏ i, ∏ k : Fin B, U j i k (markedMemoryGhostPotentialValue c i k)

def markedMemoryEdgeLocalBirthProduct
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    {hZ : ∀ z ∈ Z, IsCoprime z.1 z.2}
    (V : ℕ → J → Option Nat.Primes → ℂ) (j : ℕ)
    {s : MarkedRawState P (pads+1) B Z} (c : MarkedMemoryEdgeChoice hZ s) : ℂ :=
  ∏ i, V j i (markedMemoryEdgePotentialValue c i)

def markedMemoryHistoryLocalBirthProduct
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (U : ℕ → J → Fin B → Option Nat.Primes → ℂ) (V : ℕ → J → Option Nat.Primes → ℂ) :
    (n j : ℕ) → {s : MarkedRawState P (pads+1) B Z} → MarkedMemoryChronologicalHistory hZ n s → ℂ
  | 0,j,_,h => markedMemoryGhostLocalBirthProduct U j h
  | n+1,j,_,h => markedMemoryGhostLocalBirthProduct U j h.1 *
      markedMemoryEdgeLocalBirthProduct V j h.2.1 *
      markedMemoryHistoryLocalBirthProduct hZ U V n (j+1) h.2.2

theorem markedMemoryHistoryLocalBirthProduct_eq_visits
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (U : ℕ → J → Fin B → Option Nat.Primes → ℂ) (V : ℕ → J → Option Nat.Primes → ℂ)
    (j : ℕ) {s : MarkedRawState P (pads+1) B Z} (h : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryHistoryLocalBirthProduct hZ U V n j h =
      (∏ t : Fin (n+1), ∏ i, ∏ k : Fin B, U (j+t.1) i k (markedMemoryPotentialGhostValue hZ h t i k)) *
      (∏ t : Fin n, ∏ i, V (j+t.1) i (markedMemoryPotentialEdgeValue hZ h t i)) := by
  induction n generalizing j s with
  | zero =>
    simp only [markedMemoryHistoryLocalBirthProduct,Fin.prod_univ_succ,Fin.prod_univ_zero,
      markedMemoryPotentialGhostValue,markedMemoryGhostLocalBirthProduct,Fin.val_zero,Nat.add_zero,mul_one]
  | succ n ih =>
    rw [markedMemoryHistoryLocalBirthProduct,ih]
    simp only [Fin.prod_univ_succ,markedMemoryPotentialGhostValue,markedMemoryPotentialEdgeValue,
      Fin.cases_zero,Fin.cases_succ,Fin.val_zero,Fin.val_succ,Nat.add_zero,
      markedMemoryGhostLocalBirthProduct,markedMemoryEdgeLocalBirthProduct,Nat.add_assoc,Nat.add_comm 1]
    ring

end ArtinMatthews
