module

public import ArtinMatthews.SourceQuadraticDualDyadicWeights


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
noncomputable section

theorem quadraticDual_conductor_scale_bound {X M P G σ : ℝ}
    (hX : 0 < X) (hXM : X ≤ M) (hP : 0 < P) (hG : 1 ≤ G)
    (hσ : 0 ≤ σ) (hσ₁ : σ ≤ 1) :
    X ^ (1-σ/2) * (P/G) ^ (σ-1) ≤ G * M ^ (1-σ/2) * P ^ (σ-1) := by
  have hG0 := zero_lt_one.trans_le hG
  have hpow : (P/G) ^ (σ-1) = P ^ (σ-1) * G ^ (1-σ) := by
    rw [Real.div_rpow hP.le hG0.le]
    rw [show σ-1 = -(1-σ) by ring, Real.rpow_neg hG0.le, div_inv_eq_mul]
  have hGpow : G ^ (1-σ) ≤ G := by
    calc
      _ ≤ G ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hG (by linarith)
      _ = G := Real.rpow_one _
  rw [hpow]
  calc
    _ ≤ M ^ (1-σ/2) * (P ^ (σ-1) * G) := by
      apply mul_le_mul (Real.rpow_le_rpow hX.le hXM (by linarith))
        (mul_le_mul_of_nonneg_left hGpow (Real.rpow_nonneg hP.le _))
        (by positivity) (Real.rpow_nonneg (hX.le.trans hXM) _)
    _ = _ := by ring

theorem quadraticDual_divisor_scale_le {M N : ℝ} (hM : 0 ≤ M) (hN : 1 ≤ N) :
    M/N ≤ M := by
  exact div_le_self hM hN

end
end ArtinMatthews
