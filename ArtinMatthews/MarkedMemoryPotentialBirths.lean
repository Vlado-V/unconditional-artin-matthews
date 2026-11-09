module

public import ArtinMatthews.MarkedMemoryHistoryBirths
public import ArtinMatthews.MarkedBirthDistinctPermutation


set_option backward.privateInPublic true
@[expose] public section

/-! A fixed finite set of potential birth addresses for a literal
chronological history. Unperformed addresses have value none. The carrier
depends only on the true slot count, total memory cap and word length. -/

noncomputable section
namespace ArtinMatthews

abbrev MarkedMemoryPotentialBirth (J : Type*) (B n : ℕ) :=
  (Fin (n+1) × (J × Fin B)) ⊕ (Fin n × J)

abbrev MarkedMemoryPotentialAddress (J : Type*) (M B n : ℕ) :=
  (J × Fin M) ⊕ MarkedMemoryPotentialBirth J B n

theorem markedMemoryPotentialAddress_card {J : Type*} [Fintype J] (M B n : ℕ) :
    Fintype.card (MarkedMemoryPotentialAddress J M B n) =
      Fintype.card J*M + (n+1)*Fintype.card J*B + n*Fintype.card J := by
  simp only [MarkedMemoryPotentialAddress, MarkedMemoryPotentialBirth,
    Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

def markedMemoryPotentialOperation {J : Type*} {M B n : ℕ} :
    MarkedMemoryPotentialAddress J M B n → Option ℕ
  | Sum.inl _ => none
  | Sum.inr (Sum.inl ⟨t,_⟩) => some (2*t.1)
  | Sum.inr (Sum.inr ⟨t,_⟩) => some (2*t.1+1)

def markedMemoryGhostPotentialValue
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {M B : ℕ} {Z : Finset (ℤ × ℤ)} {hZ : ∀ z ∈ Z, IsCoprime z.1 z.2}
    {s : MarkedRawState P M B Z} (c : MarkedMemoryGhostChoice hZ s)
    (j : J) (k : Fin B) : Option Nat.Primes :=
  if h : k.1 < (c.sizes.1 j : ℕ) then some ((c.births j ⟨k.1,h⟩).1) else none

def markedMemoryEdgePotentialValue
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} {hZ : ∀ z ∈ Z, IsCoprime z.1 z.2}
    {s : MarkedRawState P (pads+1) B Z} (c : MarkedMemoryEdgeChoice hZ s) (j : J) : Option Nat.Primes :=
  if c.2.1.promotions j = none then
    some ((markedRawEdgeTargetLast (markedRawSlotEquiv c.1 s).2.2 c.2.1.promotions c.2.1.fresh j).1)
  else none

def markedMemoryPotentialGhostValue
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) :
    {n : ℕ} → {s : MarkedRawState P (pads+1) B Z} →
      MarkedMemoryChronologicalHistory hZ n s → Fin (n+1) → J → Fin B → Option Nat.Primes
  | 0,_,ghost => fun _ => markedMemoryGhostPotentialValue ghost
  | _+1,_,history => Fin.cases (markedMemoryGhostPotentialValue history.1)
      (markedMemoryPotentialGhostValue hZ history.2.2)

def markedMemoryPotentialEdgeValue
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) :
    {n : ℕ} → {s : MarkedRawState P (pads+1) B Z} →
      MarkedMemoryChronologicalHistory hZ n s → Fin n → J → Option Nat.Primes
  | 0,_,_ => Fin.elim0
  | _+1,_,history => Fin.cases (markedMemoryEdgePotentialValue history.2.1)
      (markedMemoryPotentialEdgeValue hZ history.2.2)

def markedMemoryPotentialAddressValue
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    {s : MarkedRawState P (pads+1) B Z} (history : MarkedMemoryChronologicalHistory hZ n s) :
    MarkedMemoryPotentialAddress J (pads+1) B n → Option Nat.Primes
  | Sum.inl ⟨j,k⟩ => some ((s.2.1 j k).1)
  | Sum.inr (Sum.inl ⟨t,j,k⟩) => markedMemoryPotentialGhostValue hZ history t j k
  | Sum.inr (Sum.inr ⟨t,j⟩) => markedMemoryPotentialEdgeValue hZ history t j

theorem markedMemoryGhostPotentialValue_birth
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {M B : ℕ} {Z : Finset (ℤ × ℤ)} {hZ : ∀ z ∈ Z, IsCoprime z.1 z.2}
    {s : MarkedRawState P M B Z} (c : MarkedMemoryGhostChoice hZ s)
    (j : J) (k : Fin (c.sizes.1 j : ℕ)) :
    markedMemoryGhostPotentialValue c j
      ⟨k.1, k.2.trans_le (Nat.le_of_lt_succ (c.sizes.1 j).2)⟩ =
      some (markedMemoryGhostBirthPrime c ⟨j,k⟩) := by
  simp only [markedMemoryGhostPotentialValue, dite_eq_left k.2, markedMemoryGhostBirthPrime]

theorem markedMemoryEdgePotentialValue_birth
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} {hZ : ∀ z ∈ Z, IsCoprime z.1 z.2}
    {s : MarkedRawState P (pads+1) B Z} (c : MarkedMemoryEdgeChoice hZ s)
    (j : MarkedMemoryEdgeBirthIndex c) :
    markedMemoryEdgePotentialValue c j.1 = some (markedMemoryEdgeBirthPrime c j) := by
  exact ite_eq_left j.2

end ArtinMatthews
