module

public import ArtinMatthews.MarkedMemoryPotentialBirthMap


set_option backward.privateInPublic true
@[expose] public section

/-! The performed part of the fixed potential carrier is exactly the
original dependent chronological birth type, including multiplicities. -/

noncomputable section
namespace ArtinMatthews

theorem markedMemoryPotentialBirthShift_ne_ghost_head {J : Type*} {B n : ℕ}
    (b : MarkedMemoryPotentialBirth J B n) (a : J × Fin B) :
    markedMemoryPotentialBirthShift b ≠ Sum.inl (0,a) := by
  rcases b with ⟨t,j,k⟩ | ⟨t,j⟩ <;> simp [markedMemoryPotentialBirthShift]

theorem markedMemoryPotentialBirthShift_ne_edge_head {J : Type*} {B n : ℕ}
    (b : MarkedMemoryPotentialBirth J B n) (j : J) :
    markedMemoryPotentialBirthShift b ≠ Sum.inr (0,j) := by
  rcases b with ⟨t,j,k⟩ | ⟨t,j⟩ <;> simp [markedMemoryPotentialBirthShift]

theorem markedMemoryBirthToPotential_injective
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    {s : MarkedRawState P (pads+1) B Z} (h : MarkedMemoryChronologicalHistory hZ n s) :
    Function.Injective (markedMemoryBirthToPotential hZ h) := by
  induction n generalizing s with
  | zero =>
    intro a b hab
    apply markedMemoryGhostBirthPotential_injective h
    exact congrArg Prod.snd (Sum.inl.inj hab)
  | succ n ih =>
    intro a b hab
    rcases a with a | a | a <;> rcases b with b | b | b
    · apply congrArg Sum.inl
      apply markedMemoryGhostBirthPotential_injective h.1
      exact congrArg Prod.snd (Sum.inl.inj hab)
    · cases hab
    · exact False.elim (markedMemoryPotentialBirthShift_ne_ghost_head
        (markedMemoryBirthToPotential hZ h.2.2 b) (markedMemoryGhostBirthPotential h.1 a) hab.symm)
    · cases hab
    · apply congrArg (fun a => Sum.inr (Sum.inl a))
      apply Subtype.ext
      exact congrArg Prod.snd (Sum.inr.inj hab)
    · exact False.elim (markedMemoryPotentialBirthShift_ne_edge_head
        (markedMemoryBirthToPotential hZ h.2.2 b) a.1 hab.symm)
    · exact False.elim (markedMemoryPotentialBirthShift_ne_ghost_head
        (markedMemoryBirthToPotential hZ h.2.2 a) (markedMemoryGhostBirthPotential h.1 b) hab)
    · exact False.elim (markedMemoryPotentialBirthShift_ne_edge_head
        (markedMemoryBirthToPotential hZ h.2.2 a) b.1 hab)
    · apply congrArg (fun a => Sum.inr (Sum.inr a))
      exact ih h.2.2 (markedMemoryPotentialBirthShift_injective hab)

theorem markedMemoryGhostPotentialValue_has_birth
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {M B : ℕ} {Z : Finset (ℤ × ℤ)} {hZ : ∀ z ∈ Z, IsCoprime z.1 z.2}
    {s : MarkedRawState P M B Z} (c : MarkedMemoryGhostChoice hZ s) (a : J × Fin B)
    (ha : markedMemoryGhostPotentialValue c a.1 a.2 ≠ none) :
    ∃ b : MarkedMemoryGhostBirthIndex c, markedMemoryGhostBirthPotential c b = a := by
  have hk : a.2.1 < (c.sizes.1 a.1 : ℕ) := by
    by_contra hk
    exact ha (dite_eq_right hk)
  refine ⟨⟨a.1,⟨a.2.1,hk⟩⟩,?_⟩
  exact Prod.ext rfl (Fin.ext rfl)

theorem markedMemoryEdgePotentialValue_has_birth
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} {hZ : ∀ z ∈ Z, IsCoprime z.1 z.2}
    {s : MarkedRawState P (pads+1) B Z} (c : MarkedMemoryEdgeChoice hZ s) (j : J)
    (hj : markedMemoryEdgePotentialValue c j ≠ none) : c.2.1.promotions j = none := by
  by_contra hn
  exact hj (ite_eq_right hn)

theorem markedMemoryBirthToPotential_covers
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    {s : MarkedRawState P (pads+1) B Z} (h : MarkedMemoryChronologicalHistory hZ n s)
    (b : MarkedMemoryPotentialBirth J B n)
    (hb : markedMemoryPotentialAddressValue hZ h (Sum.inr b) ≠ none) :
    ∃ a : MarkedMemoryHistoryBirths hZ h, markedMemoryBirthToPotential hZ h a = b := by
  induction n generalizing s with
  | zero =>
    rcases b with ⟨t,j,k⟩ | ⟨t,j⟩
    · have ht : t = 0 := Fin.ext (by omega)
      subst t
      obtain ⟨a,ha⟩ := markedMemoryGhostPotentialValue_has_birth h (j,k) hb
      refine ⟨a,?_⟩
      change Sum.inl (0,markedMemoryGhostBirthPotential h a) = Sum.inl (0,(j,k))
      rw [ha]
    · exact Fin.elim0 t
  | succ n ih =>
    rcases b with ⟨t,j,k⟩ | ⟨t,j⟩
    · revert hb
      refine Fin.cases ?_ (fun t => ?_) t
      · intro hb
        obtain ⟨a,ha⟩ := markedMemoryGhostPotentialValue_has_birth h.1 (j,k) hb
        refine ⟨Sum.inl a,?_⟩
        change Sum.inl (0,markedMemoryGhostBirthPotential h.1 a) = Sum.inl (0,(j,k))
        rw [ha]
      · intro hb
        change markedMemoryPotentialAddressValue hZ h
          (Sum.inr (markedMemoryPotentialBirthShift (Sum.inl (t,(j,k))))) ≠ none at hb
        rw [markedMemoryPotentialBirthShift_value] at hb
        obtain ⟨a,ha⟩ := ih h.2.2 (Sum.inl (t,(j,k))) hb
        refine ⟨Sum.inr (Sum.inr a),?_⟩
        change markedMemoryPotentialBirthShift (markedMemoryBirthToPotential hZ h.2.2 a) = _
        rw [ha]
        rfl
    · revert hb
      refine Fin.cases ?_ (fun t => ?_) t
      · intro hb
        have hp := markedMemoryEdgePotentialValue_has_birth h.2.1 j hb
        exact ⟨Sum.inr (Sum.inl ⟨j,hp⟩),rfl⟩
      · intro hb
        change markedMemoryPotentialAddressValue hZ h
          (Sum.inr (markedMemoryPotentialBirthShift (Sum.inr (t,j)))) ≠ none at hb
        rw [markedMemoryPotentialBirthShift_value] at hb
        obtain ⟨a,ha⟩ := ih h.2.2 (Sum.inr (t,j)) hb
        refine ⟨Sum.inr (Sum.inr a),?_⟩
        change markedMemoryPotentialBirthShift (markedMemoryBirthToPotential hZ h.2.2 a) = _
        rw [ha]
        rfl

def markedMemoryBirthPerformedAddress
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    {s : MarkedRawState P (pads+1) B Z} (h : MarkedMemoryChronologicalHistory hZ n s)
    (b : MarkedMemoryHistoryBirths hZ h) :
    {a : MarkedMemoryPotentialBirth J B n // markedMemoryPotentialAddressValue hZ h (Sum.inr a) ≠ none} :=
  ⟨markedMemoryBirthToPotential hZ h b, by rw [markedMemoryBirthToPotential_prime]; simp⟩

def markedMemoryPerformedBirthEquiv
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    {s : MarkedRawState P (pads+1) B Z} (h : MarkedMemoryChronologicalHistory hZ n s) :
    MarkedMemoryHistoryBirths hZ h ≃
      {a : MarkedMemoryPotentialBirth J B n // markedMemoryPotentialAddressValue hZ h (Sum.inr a) ≠ none} :=
  Equiv.ofBijective (markedMemoryBirthPerformedAddress hZ h) ⟨by
    intro a b hab
    exact markedMemoryBirthToPotential_injective hZ h (congrArg Subtype.val hab), by
    intro a
    obtain ⟨b,hb⟩ := markedMemoryBirthToPotential_covers hZ h a.1 a.2
    exact ⟨b,Subtype.ext hb⟩⟩

end ArtinMatthews
