module

public import ArtinMatthews.MarkedRepresentedDivisors


set_option backward.privateInPublic true
@[expose] public section

/-! Exact reciprocal coefficient mass for repeated marking bands. -/

namespace ArtinMatthews

open scoped BigOperators

/-- Diagonal selected pairs contribute only one reciprocal prime factor. -/
theorem sum_diagonal_offDiagonal {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (w : ι → ℝ) (c : ℝ) :
    (∑ p ∈ P, ∑ q ∈ P, if p = q then w p else c * w p * w q) =
      (∑ p ∈ P, w p) + c * ((∑ p ∈ P, w p) ^ 2 - ∑ p ∈ P, (w p) ^ 2) := by
  have hrow (p : ι) (hp : p ∈ P) :
      (∑ q ∈ P, if p = q then w p else c * w p * w q) =
        c * w p * (∑ q ∈ P, w q) + w p - c * (w p) ^ 2 := by
    calc
      _ = ∑ q ∈ P, (c * w p * w q + if p = q then w p - c * (w p) ^ 2 else 0) := by
        apply Finset.sum_congr rfl
        intro q _
        by_cases hpq : p = q
        · subst q
          simp only [ite_true]
          ring
        · simp [hpq]
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp [hp]
        ring
  rw [Finset.sum_congr rfl hrow]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

noncomputable def representedPairReciprocalMass (P : Finset ℕ) (ρ : ℝ) : ℝ :=
  ∑ p ∈ P, ∑ q ∈ P,
    ρ ^ (2 * (({p, q} : Finset ℕ).card - 1)) /
      ∏ r ∈ ({p, q} : Finset ℕ), (r : ℝ)

/-- The exact repeated-array mass from the represented-union expansion.
The `V` term is the collision contribution; the remaining term counts
ordered pairs of distinct primes. -/
theorem representedPairReciprocalMass_eq (P : Finset ℕ) (ρ : ℝ) :
    representedPairReciprocalMass P ρ = bandReciprocalMass P +
      ρ ^ 2 * ((bandReciprocalMass P) ^ 2 - ∑ p ∈ P, (1 / (p : ℝ)) ^ 2) := by
  unfold representedPairReciprocalMass bandReciprocalMass
  rw [← sum_diagonal_offDiagonal P (fun p => 1 / (p : ℝ)) (ρ ^ 2)]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  by_cases hpq : p = q
  · subst q
    simp
  · simp [hpq, Finset.card_pair hpq, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

theorem representedPairReciprocalMass_nonneg (P : Finset ℕ) (ρ : ℝ) :
    0 ≤ representedPairReciprocalMass P ρ := by
  unfold representedPairReciprocalMass
  apply Finset.sum_nonneg
  intro p _
  apply Finset.sum_nonneg
  intro q _
  apply div_nonneg
  · rw [pow_mul]
    positivity
  · exact Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _)

/-- A uniform positive lower bound on `V` bounds the normalized reciprocal
mass of represented unions, irrespective of the particular prime band. -/
theorem representedPairReciprocalMass_normalized_le (P : Finset ℕ) (ρ : ℝ)
    {v : ℝ} (hv : 0 < v) (hV : v ≤ bandReciprocalMass P) :
    representedPairReciprocalMass P ρ / (bandReciprocalMass P) ^ 2 ≤ 1 / v + ρ ^ 2 := by
  have hpos : 0 < bandReciprocalMass P := hv.trans_le hV
  have hs : 0 ≤ ∑ p ∈ P, (1 / (p : ℝ)) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [representedPairReciprocalMass_eq]
  calc
    _ ≤ (bandReciprocalMass P + ρ ^ 2 * (bandReciprocalMass P) ^ 2) /
        (bandReciprocalMass P) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      nlinarith [sq_nonneg ρ]
    _ = 1 / bandReciprocalMass P + ρ ^ 2 := by field_simp
    _ ≤ 1 / v + ρ ^ 2 := add_le_add (one_div_le_one_div_of_le hv hV) le_rfl

end ArtinMatthews
