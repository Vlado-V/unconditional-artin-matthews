module

public import ArtinMatthews.MarkedMemoryHistoryPrimeWeight


set_option backward.privateInPublic true
@[expose] public section

/-! Literal scalar factors of one actual ghost choice. Every old pending
index is retained: a deletion pays -(1-q), a surviving hit pays q, and a
surviving nonhit pays one. Each performed birth pays -(1-q). -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedMemoryGhostScalar_prod_partition {α : Type*} [Fintype α] [DecidableEq α]
    (D H : Finset α) (a b : ℝ) :
    (∏ k : α, if k ∈ D then a else if k ∈ H then b else 1) =
      a ^ D.card * b ^ (H \ D).card := by
  have he (k : α) : (if k ∈ D then a else if k ∈ H then b else 1) =
      (if k ∈ D then a else 1) * (if k ∈ H \ D then b else 1) := by
    by_cases hd : k ∈ D <;> by_cases hh : k ∈ H <;> simp [hd, hh]
  simp_rw [he]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_ite_mem_eq, Finset.prod_const]

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {M B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P M B Z)
  (ghost : MarkedMemoryGhostChoice hZ s)

abbrev MarkedMemoryGhostScalarEvent :=
  (Σ band : J, Fin (s.2.2.1.1 band : ℕ)) ⊕ MarkedMemoryGhostBirthIndex ghost

def markedMemoryGhostOldScalar (q : ℝ) (band : J) (k : Fin (s.2.2.1.1 band : ℕ)) : ℝ :=
  if k ∈ ghost.deletion band then -(1-q)
  else if k ∈ markedRawGroupHitIndices s.2.2 band s.1.1 (hZ _ s.1.2) then q else 1

def markedMemoryGhostEventScalar (q : ℝ) : MarkedMemoryGhostScalarEvent hZ s ghost → ℝ :=
  Sum.elim (fun old => markedMemoryGhostOldScalar hZ s ghost q old.1 old.2) (fun _ => -(1-q))

def markedMemoryGhostScalarProduct (q : ℝ) : ℝ :=
  ∏ event : MarkedMemoryGhostScalarEvent hZ s ghost, markedMemoryGhostEventScalar hZ s ghost q event

def markedMemoryGhostBirthFactorial : ℝ :=
  ∏ band : J, ((ghost.sizes.1 band : ℕ).factorial : ℝ)

theorem markedMemoryGhostOldScalar_deleted (q : ℝ) (band : J)
    (k : Fin (s.2.2.1.1 band : ℕ)) (hk : k ∈ ghost.deletion band) :
    markedMemoryGhostOldScalar hZ s ghost q band k = -(1-q) := by
  exact ite_eq_left hk

theorem markedMemoryGhostOldScalar_hit (q : ℝ) (band : J)
    (k : Fin (s.2.2.1.1 band : ℕ)) (hk : k ∉ ghost.deletion band)
    (hh : k ∈ markedRawGroupHitIndices s.2.2 band s.1.1 (hZ _ s.1.2)) :
    markedMemoryGhostOldScalar hZ s ghost q band k = q := by
  unfold markedMemoryGhostOldScalar
  rw [ite_eq_right hk, ite_eq_left hh]

theorem markedMemoryGhostOldScalar_nonhit (q : ℝ) (band : J)
    (k : Fin (s.2.2.1.1 band : ℕ))
    (hh : k ∉ markedRawGroupHitIndices s.2.2 band s.1.1 (hZ _ s.1.2)) :
    markedMemoryGhostOldScalar hZ s ghost q band k = 1 := by
  have hk : k ∉ ghost.deletion band := fun hk => hh (ghost.allowed band hk)
  unfold markedMemoryGhostOldScalar
  rw [ite_eq_right hk, ite_eq_right hh]

theorem markedMemoryGhostScalarProduct_eq (q : ℝ) :
    markedMemoryGhostScalarProduct hZ s ghost q =
      ∏ band : J, (-(1-q)) ^ (ghost.deletion band).card *
        q ^ (markedRawGroupHitIndices s.2.2 band s.1.1 (hZ _ s.1.2) \ ghost.deletion band).card *
        (-(1-q)) ^ (ghost.sizes.1 band : ℕ) := by
  unfold markedMemoryGhostScalarProduct
  rw [Fintype.prod_sum_type]
  change (∏ old : Σ band : J, Fin (s.2.2.1.1 band : ℕ),
      markedMemoryGhostOldScalar hZ s ghost q old.1 old.2) *
    (∏ _birth : Σ band : J, Fin (ghost.sizes.1 band : ℕ), -(1-q)) = _
  rw [Fintype.prod_sigma, Fintype.prod_sigma]
  have ho : (∏ band : J, ∏ k : Fin (s.2.2.1.1 band : ℕ),
      markedMemoryGhostOldScalar hZ s ghost q band k) =
      ∏ band : J, (-(1-q)) ^ (ghost.deletion band).card *
        q ^ (markedRawGroupHitIndices s.2.2 band s.1.1 (hZ _ s.1.2) \ ghost.deletion band).card := by
    apply Finset.prod_congr rfl
    intro band _
    unfold markedMemoryGhostOldScalar
    exact markedMemoryGhostScalar_prod_partition (ghost.deletion band)
      (markedRawGroupHitIndices s.2.2 band s.1.1 (hZ _ s.1.2)) (-(1-q)) q
  rw [ho]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Finset.prod_mul_distrib]

variable {pads : ℕ}

theorem markedMemoryGhostResidual_scalar
    (s : MarkedRawState P (pads+1) B Z) (ghost : MarkedMemoryGhostChoice hZ s) (q : ℝ) :
    markedMemoryGhostResidual hZ q s ghost =
      markedMemoryGhostScalarProduct hZ s ghost q / markedMemoryGhostBirthFactorial hZ s ghost := by
  rw [markedMemoryGhostScalarProduct_eq]
  unfold markedMemoryGhostResidual markedMemoryGhostBirthFactorial
  exact Finset.prod_div_distrib (s := Finset.univ)
    (f := fun band : J => (-(1-q)) ^ (ghost.deletion band).card *
      q ^ (markedRawGroupHitIndices s.2.2 band s.1.1 (hZ _ s.1.2) \ ghost.deletion band).card *
      (-(1-q)) ^ (ghost.sizes.1 band : ℕ))
    (g := fun band : J => ((ghost.sizes.1 band : ℕ).factorial : ℝ))

end
end ArtinMatthews
