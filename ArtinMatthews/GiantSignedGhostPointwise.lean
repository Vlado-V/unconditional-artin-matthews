module

public import ArtinMatthews.GiantSignedGhostConvergence


set_option backward.privateInPublic true
@[expose] public section

/-! The true signed ghost row is dominated on exponential memory weights,
with every birth count and indexed old deletion included. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem giantSignedGhostGroupApply_norm_le {P : Finset ℕ}
    (ν : P → ℝ) (hν : ∀ p, 0 ≤ ν p) (A C D : ℂ)
    (f : GiantSignedGroupMemory P → ℂ) (B v : ℝ) (hv : 0 < v)
    (hf : ∀ x, ‖f x‖ ≤ B * v ^ x.1) (m : GiantSignedGroupMemory P) :
    ‖giantSignedGhostGroupApply ν A C D f m‖ ≤
      B * v ^ m.1 * Real.exp (‖C‖ * (∑ p : P, ν p) * v) *
        (‖A‖ + ‖D‖ / v) ^ (giantSignedGhostZeroIndices m).card := by
  classical
  let E := Real.exp (‖C‖ * (∑ p : P, ν p) * v)
  have hp (deleted : Finset (Fin m.1)) : v ^ (m.1 - deleted.card) = v ^ m.1 / v ^ deleted.card := by
    rw [eq_div_iff (pow_ne_zero _ (ne_of_gt hv)), ← pow_add]
    congr 1
    have hc : deleted.card ≤ m.1 := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.subset_univ deleted)
    omega
  change ‖∑ deleted ∈ (giantSignedGhostZeroIndices m).powerset,
    D ^ deleted.card * A ^ ((giantSignedGhostZeroIndices m).card - deleted.card) *
      ∑' b, giantSignedGhostBirthContribution ν C m deleted f b‖ ≤ _
  calc
    _ ≤ ∑ deleted ∈ (giantSignedGhostZeroIndices m).powerset,
        ‖D ^ deleted.card * A ^ ((giantSignedGhostZeroIndices m).card - deleted.card) *
          ∑' b, giantSignedGhostBirthContribution ν C m deleted f b‖ := norm_sum_le _ _
    _ ≤ ∑ deleted ∈ (giantSignedGhostZeroIndices m).powerset,
        ‖D‖ ^ deleted.card * ‖A‖ ^ ((giantSignedGhostZeroIndices m).card - deleted.card) *
          ((B * v ^ (m.1 - deleted.card)) * E) := by
      apply Finset.sum_le_sum
      intro deleted _
      rw [norm_mul, norm_mul, norm_pow, norm_pow]
      exact mul_le_mul_of_nonneg_left
        (giantSignedGhostBirthContribution_tsum_norm_le ν hν C m deleted f B v hf)
        (mul_nonneg (pow_nonneg (norm_nonneg _) _) (pow_nonneg (norm_nonneg _) _))
    _ = B * v ^ m.1 * E * ∑ deleted ∈ (giantSignedGhostZeroIndices m).powerset,
        (‖D‖ / v) ^ deleted.card * ‖A‖ ^ ((giantSignedGhostZeroIndices m).card - deleted.card) := by
      conv_rhs => rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro deleted _
      rw [hp, div_pow]
      ring
    _ = _ := by rw [Finset.sum_pow_mul_eq_add_pow, add_comm (‖D‖ / v) ‖A‖]

theorem giantSignedGhostGroupApply_weight_bound {P : Finset ℕ}
    (ν : P → ℝ) (hν : ∀ p, 0 ≤ ν p) (A C D : ℂ)
    (f : GiantSignedGroupMemory P → ℂ) (B v : ℝ) (hB : 0 ≤ B) (hv : 0 < v)
    (hcontract : ‖A‖ + ‖D‖ / v ≤ 1)
    (hf : ∀ x, ‖f x‖ ≤ B * v ^ x.1) (m : GiantSignedGroupMemory P) :
    ‖giantSignedGhostGroupApply ν A C D f m‖ ≤
      B * v ^ m.1 * Real.exp (‖C‖ * (∑ p : P, ν p) * v) := by
  apply (giantSignedGhostGroupApply_norm_le ν hν A C D f B v hv hf m).trans
  exact mul_le_of_le_one_right
    (mul_nonneg (mul_nonneg hB (pow_nonneg hv.le _)) (le_of_lt (Real.exp_pos _)))
    (pow_le_one₀ (add_nonneg (norm_nonneg _) (div_nonneg (norm_nonneg _) hv.le)) hcontract)

end
end ArtinMatthews
