module

public import ArtinMatthews.SourceQuadraticPoissonErrorSeparation


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open scoped BigOperators
noncomputable section

/-- Small positive Mellin exponents fit into one prescribed loss. -/
theorem quadraticSmall_power_absorb {M K P η σ ε : ℝ}
    (hM : 1 ≤ M) (hP : 1 ≤ P) (hK : 0 ≤ K) (hKM : K ≤ M)
    (hη : 0 ≤ η) (hσ : 0 ≤ σ) (hloss : 3 * η + σ / 2 ≤ ε) :
    M ^ (σ / 2) * (K * P) ^ η * (2 * P) ^ (2 * η) ≤
      2 ^ (2 * η) * (M * P) ^ ε := by
  have hM0 := zero_lt_one.trans_le hM
  have hP0 := zero_lt_one.trans_le hP
  have hT0 := mul_pos hM0 hP0
  have hT := one_le_mul_of_one_le_of_one_le hM hP
  have hMT : M ≤ M * P := le_mul_of_one_le_right hM0.le hP
  have hPT : P ≤ M * P := le_mul_of_one_le_left hP0.le hM
  calc
    _ = 2 ^ (2 * η) * (M ^ (σ / 2) * (K * P) ^ η * P ^ (2 * η)) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hP0.le]
      ring
    _ ≤ 2 ^ (2 * η) * ((M * P) ^ (σ / 2) * (M * P) ^ η * (M * P) ^ (2 * η)) := by
      gcongr
    _ = 2 ^ (2 * η) * (M * P) ^ (3 * η + σ / 2) := by
      rw [← Real.rpow_add hT0, ← Real.rpow_add hT0]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hT hloss) (by positivity)

theorem quadraticSmall_cutoff_power {M K α : ℝ} (hK : 1 ≤ K) (hKM : K ≤ M) :
    K ^ α ≤ Real.sqrt M * K ^ (α - 1 / 2) := by
  have hK0 := zero_lt_one.trans_le hK
  calc
    _ = Real.sqrt K * K ^ (α - 1 / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hK0]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hKM) (by positivity)

end
end ArtinMatthews
