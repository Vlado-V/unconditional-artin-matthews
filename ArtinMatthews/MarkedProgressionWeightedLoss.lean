module

public import ArtinMatthews.MarkedProgressionWeighted
public import ArtinMatthews.MarkedProgressionLocalLoss


set_option backward.privateInPublic true
@[expose] public section

/-! The local coprimality loss for prime-dependent damping parameters.
The numerator is the actual product of the retained prime weights;
the represented-divisor reciprocal and the depth-uniform exponential
mass bound are kept explicit. -/

namespace ArtinMatthews

open OAI.Erdos970.NumberTheoryLean
open scoped BigOperators

/-- Exact reciprocal mass for all retained weighted layers. -/
theorem marked_weighted_selected_partial_reciprocal_mass (P S : Finset ℕ)
    (k : ℕ) (θ : ℕ → ℝ) :
    (∑ j ∈ Finset.range (k + 1), ∑ T ∈ (P \ S).powersetCard j,
      (∏ p ∈ T, θ p) / (∏ p ∈ S ∪ T, p : ℕ)) =
      (1 / (∏ p ∈ S, p : ℕ)) *
        ∑ j ∈ Finset.range (k + 1),
          BonferroniDensity.elementarySum (P \ S) (fun p => θ p / (p : ℝ)) j := by
  simp_rw [marked_weighted_selected_reciprocal_mass]
  rw [Finset.mul_sum]

/-- Prime-dependent damping still gives a depth-uniform reciprocal mass. -/
theorem marked_weighted_selected_partial_reciprocal_mass_le_exp (P S : Finset ℕ)
    (k : ℕ) (θ : ℕ → ℝ) (hθ : ∀ p ∈ P, 0 ≤ θ p) {V : ℝ}
    (hmass : ∑ p ∈ P \ S, θ p / (p : ℝ) ≤ V) :
    (∑ j ∈ Finset.range (k + 1), ∑ T ∈ (P \ S).powersetCard j,
      (∏ p ∈ T, θ p) / (∏ p ∈ S ∪ T, p : ℕ)) ≤
      (1 / (∏ p ∈ S, p : ℕ)) * Real.exp V := by
  rw [marked_weighted_selected_partial_reciprocal_mass]
  exact mul_le_mul_of_nonneg_left
    (marked_weighted_elementary_partial_sum_le_exp (P \ S) θ k
      (fun p hp => hθ p (Finset.mem_sdiff.mp hp).1) hmass) (by positivity)

/-- Full truncated local coprimality loss with the actual product weights.
Only nonnegativity of the damping is required for this estimate. -/
theorem marked_weighted_selected_truncated_local_loss_le (P S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) (k : ℕ)
    (θ : ℕ → ℝ) (hθ : ∀ p ∈ P, 0 ≤ θ p)
    {y V : ℝ} (hy : 0 < y) (hmin : ∀ p ∈ P, y ≤ (p : ℝ))
    (hmass : ∑ p ∈ P \ S, θ p / (p : ℝ) ≤ V) :
    (∑ j ∈ Finset.range (k + 1), ∑ T ∈ (P \ S).powersetCard j,
      ((∏ p ∈ T, θ p) / (∏ p ∈ S ∪ T, p : ℕ)) *
        ∑ q ∈ (∏ p ∈ S ∪ T, p : ℕ).primeFactors, 1 / (q : ℝ)) ≤
      (((S.card + k : ℕ) : ℝ) / y) *
        (1 / (∏ p ∈ S, p : ℕ)) * Real.exp V := by
  classical
  let A : ℝ := ((S.card + k : ℕ) : ℝ) / y
  have hA : 0 ≤ A := by dsimp [A]; positivity
  calc
    _ ≤ ∑ j ∈ Finset.range (k + 1), ∑ T ∈ (P \ S).powersetCard j,
        ((∏ p ∈ T, θ p) / (∏ p ∈ S ∪ T, p : ℕ)) * A := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro T hT
      obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hT
      have hTk : T.card ≤ k := by
        rw [hcard]
        exact Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hweight : 0 ≤ ∏ p ∈ T, θ p :=
        Finset.prod_nonneg fun p hp => hθ p (Finset.mem_sdiff.mp (hsub hp)).1
      exact mul_le_mul_of_nonneg_left
        (marked_union_prime_reciprocal_le P S T hP hS hsub k hTk hy hmin)
        (div_nonneg hweight (Nat.cast_nonneg _))
    _ = A * (∑ j ∈ Finset.range (k + 1), ∑ T ∈ (P \ S).powersetCard j,
        (∏ p ∈ T, θ p) / (∏ p ∈ S ∪ T, p : ℕ)) := by
      simp_rw [← Finset.sum_mul]
      rw [mul_comm]
    _ ≤ A * ((1 / (∏ p ∈ S, p : ℕ)) * Real.exp V) :=
      mul_le_mul_of_nonneg_left
        (marked_weighted_selected_partial_reciprocal_mass_le_exp P S k θ hθ hmass) hA
    _ = _ := by rw [mul_assoc]

end ArtinMatthews
