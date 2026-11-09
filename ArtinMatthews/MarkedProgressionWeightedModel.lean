module

public import ArtinMatthews.MarkedProgressionWeightedPolynomial


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite Euler model for a selected weighted residual. -/

namespace ArtinMatthews

open OAI.Erdos970.NumberTheoryLean
open scoped BigOperators

noncomputable def markedWeightedModel (P S : Finset ℕ) (θ : ℕ → ℝ) : ℝ :=
  (1 / (∏ p ∈ S, p : ℕ)) * ∏ p ∈ P \ S, (1 - θ p / (p : ℝ))

noncomputable def markedWeightedTailModel (P S : Finset ℕ) (θ : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ T ∈ (P \ S).powersetCard k, (∏ p ∈ T, θ p) / (∏ p ∈ S ∪ T, p : ℕ)

/-- The selected Euler model has the same positive Bonferroni error as the
arithmetic residual; the selected reciprocal factor is exact. -/
theorem markedWeightedModel_truncation_error (P S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (θ : ℕ → ℝ)
    (hθ : ∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) (m : ℕ) :
    |markedWeightedModel P S θ -
      ∑ i ∈ markedWeightedIndices P S (2 * m),
        markedWeightedCoefficient θ i / (markedWeightedDivisor S i : ℝ)| ≤
      markedWeightedTailModel P S θ (2 * m + 1) := by
  rw [markedWeightedCoefficient_reciprocal_sum]
  unfold markedWeightedModel markedWeightedTailModel
  rw [marked_weighted_selected_reciprocal_mass]
  have hb (p : ℕ) (hp : p ∈ P \ S) :
      0 ≤ θ p / (p : ℝ) ∧ θ p / (p : ℝ) ≤ 1 := by
    have hpP := (Finset.mem_sdiff.mp hp).1
    have hpos : (0 : ℝ) < p := by exact_mod_cast (hP p hpP).pos
    constructor
    · exact div_nonneg (hθ p hpP).1 hpos.le
    · apply (div_le_one hpos).mpr
      exact (hθ p hpP).2.trans (by exact_mod_cast (hP p hpP).one_lt.le)
  have h := BonferroniDensity.densityPolynomial_bounds (P \ S) (fun p => θ p / (p : ℝ))
    (fun p hp => (hb p hp).1) (fun p hp => (hb p hp).2) m
  have hg := BonferroniDensity.densityPolynomial_gap m (P \ S) (fun p => θ p / (p : ℝ))
  have hc : 0 ≤ (1 : ℝ) / (∏ p ∈ S, p : ℕ) := by positivity
  rw [← mul_sub, abs_mul, abs_of_nonneg hc, abs_of_nonpos (sub_nonpos.mpr h.2)]
  apply mul_le_mul_of_nonneg_left _ hc
  linarith [h.1]

end ArtinMatthews
