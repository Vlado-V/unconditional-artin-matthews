module

public import ArtinMatthews.MarkedMemoryPotentialBirths


set_option backward.privateInPublic true
@[expose] public section

/-! Actual performed birth identities map into the fixed potential
carrier without changing prime values. Tail addresses advance their
operation time; no placeholder prime is attached to an absent birth. -/

noncomputable section
namespace ArtinMatthews

def markedMemoryPotentialBirthShift {J : Type*} {B n : ℕ} :
    MarkedMemoryPotentialBirth J B n → MarkedMemoryPotentialBirth J B (n+1)
  | Sum.inl ⟨t,j,k⟩ => Sum.inl ⟨t.succ,j,k⟩
  | Sum.inr ⟨t,j⟩ => Sum.inr ⟨t.succ,j⟩

theorem markedMemoryPotentialBirthShift_injective {J : Type*} {B n : ℕ} :
    Function.Injective (markedMemoryPotentialBirthShift (J := J) (B := B) (n := n)) := by
  intro a b h
  rcases a with ⟨t,j,k⟩ | ⟨t,j⟩ <;> rcases b with ⟨u,l,i⟩ | ⟨u,l⟩ <;>
    simp_all [markedMemoryPotentialBirthShift]

def markedMemoryGhostBirthPotential
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {M B : ℕ} {Z : Finset (ℤ × ℤ)} {hZ : ∀ z ∈ Z, IsCoprime z.1 z.2}
    {s : MarkedRawState P M B Z} (c : MarkedMemoryGhostChoice hZ s)
    (b : MarkedMemoryGhostBirthIndex c) : J × Fin B :=
  (b.1, ⟨b.2.1,b.2.2.trans_le (Nat.le_of_lt_succ (c.sizes.1 b.1).2)⟩)

theorem markedMemoryGhostBirthPotential_injective
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {M B : ℕ} {Z : Finset (ℤ × ℤ)} {hZ : ∀ z ∈ Z, IsCoprime z.1 z.2}
    {s : MarkedRawState P M B Z} (c : MarkedMemoryGhostChoice hZ s) :
    Function.Injective (markedMemoryGhostBirthPotential c) := by
  intro a b h
  rcases a with ⟨j,k⟩
  rcases b with ⟨l,i⟩
  have hj : j = l := congrArg Prod.fst h
  subst l
  have hk : k = i := Fin.ext (congrArg (fun a => a.2.1) h)
  subst i
  rfl

def markedMemoryBirthToPotential
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) :
    {n : ℕ} → {s : MarkedRawState P (pads+1) B Z} →
      (h : MarkedMemoryChronologicalHistory hZ n s) →
      MarkedMemoryHistoryBirths hZ h → MarkedMemoryPotentialBirth J B n
  | 0,_,ghost,b => Sum.inl ⟨0,markedMemoryGhostBirthPotential ghost b⟩
  | _+1,_,h,Sum.inl b => Sum.inl ⟨0,markedMemoryGhostBirthPotential h.1 b⟩
  | _+1,_,_,Sum.inr (Sum.inl b) => Sum.inr ⟨0,b.1⟩
  | _+1,_,h,Sum.inr (Sum.inr b) => markedMemoryPotentialBirthShift (markedMemoryBirthToPotential hZ h.2.2 b)

theorem markedMemoryPotentialBirthShift_value
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    {s : MarkedRawState P (pads+1) B Z} (h : MarkedMemoryChronologicalHistory hZ (n+1) s)
    (b : MarkedMemoryPotentialBirth J B n) :
    markedMemoryPotentialAddressValue hZ h (Sum.inr (markedMemoryPotentialBirthShift b)) =
      markedMemoryPotentialAddressValue hZ h.2.2 (Sum.inr b) := by
  rcases b with ⟨t,j,k⟩ | ⟨t,j⟩ <;> rfl

theorem markedMemoryBirthToPotential_prime
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    {s : MarkedRawState P (pads+1) B Z} (h : MarkedMemoryChronologicalHistory hZ n s)
    (b : MarkedMemoryHistoryBirths hZ h) :
    markedMemoryPotentialAddressValue hZ h (Sum.inr (markedMemoryBirthToPotential hZ h b)) =
      some (markedMemoryHistoryBirthPrime hZ h b) := by
  induction n generalizing s with
  | zero => exact markedMemoryGhostPotentialValue_birth h b.1 b.2
  | succ n ih =>
    rcases b with b | b | b
    · exact markedMemoryGhostPotentialValue_birth h.1 b.1 b.2
    · exact markedMemoryEdgePotentialValue_birth h.2.1 b
    · change markedMemoryPotentialAddressValue hZ h
        (Sum.inr (markedMemoryPotentialBirthShift (markedMemoryBirthToPotential hZ h.2.2 b))) = _
      rw [markedMemoryPotentialBirthShift_value]
      exact ih h.2.2 b

end ArtinMatthews
