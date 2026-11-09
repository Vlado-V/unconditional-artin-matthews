module

public import ArtinMatthews.SourceQuadraticDualRowInterval


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
noncomputable section

theorem quadraticDual_dyadic_weights {L R K P α σ : ℝ}
    (hL : 0 < L) (hR : 0 < R) (hRK : R ≤ K) (hLR : L ≤ 2 * R)
    (hP : 0 ≤ P) (hσ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (hα : σ / 2 ≤ α) :
    R ^ (-(σ / 2)) * (P + (2 * R) ^ α) ≤
      2 * P * L ^ (-(σ / 2)) + (2 : ℝ) ^ α * K ^ (α - σ / 2) := by
  have hfirst : R ^ (-(σ / 2)) ≤ 2 * L ^ (-(σ / 2)) := by
    calc
      _ ≤ (L / 2) ^ (-(σ / 2)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
      _ = L ^ (-(σ / 2)) * (2 : ℝ) ^ (σ / 2) := by
        rw [Real.div_rpow hL.le (by norm_num)]
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
      _ ≤ L ^ (-(σ / 2)) * 2 := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hL.le _)
        calc
          _ ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 2 := Real.rpow_one _
      _ = _ := mul_comm _ _
  have hsecond : R ^ (-(σ / 2)) * (2 * R) ^ α ≤
      (2 : ℝ) ^ α * K ^ (α - σ / 2) := by
    rw [Real.mul_rpow (by norm_num) hR.le]
    calc
      _ = (2 : ℝ) ^ α * R ^ (α - σ / 2) := by
        rw [show α - σ / 2 = α + -(σ / 2) by ring, Real.rpow_add hR]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hR.le hRK (by linarith)) (Real.rpow_nonneg (by norm_num) _)
  calc
    _ = P * R ^ (-(σ / 2)) + R ^ (-(σ / 2)) * (2 * R) ^ α := by ring
    _ ≤ P * (2 * L ^ (-(σ / 2))) + (2 : ℝ) ^ α * K ^ (α - σ / 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hfirst hP) hsecond
    _ = _ := by ring

end
end ArtinMatthews
