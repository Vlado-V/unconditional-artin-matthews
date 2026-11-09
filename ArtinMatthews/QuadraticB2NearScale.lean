module

public import ArtinMatthews.QuadraticB2PoissonCutoff


set_option backward.privateInPublic true
@[expose] public section

/-! The near and small-row regime of Theorem 4.3 follows directly from
E_alpha, retaining the same mixed scale term. -/
namespace ArtinMatthews.QuadraticScale

noncomputable section

theorem nearScale_main_bound {M N a δ : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N)
    (ha : 1 ≤ a) (hδ : 0 ≤ δ) (hnear : M ≤ 2 * N * (M * N) ^ δ) :
    M + N ^ a ≤ (1 + (2 : ℝ) ^ (a - 1)) * (M * N) ^ (δ * (a - 1)) *
      poissonMainScale M N a := by
  let T := M * N
  let V := N ^ (2 * a - 1) * M ^ (1 - a)
  let U := T ^ (δ * (a - 1))
  have hM0 := zero_lt_one.trans_le hM
  have hN0 := zero_lt_one.trans_le hN
  have hT : 1 ≤ T := one_le_mul_of_one_le_of_one_le hM hN
  have hU : 1 ≤ U := Real.one_le_rpow hT (mul_nonneg hδ (by linarith))
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hratio : M / N ≤ 2 * T ^ δ := by
    apply (div_le_iff₀ hN0).mpr
    convert hnear using 1; ring
  have hpow : (M / N) ^ (a - 1) ≤ (2 : ℝ) ^ (a - 1) * U := by
    have h := Real.rpow_le_rpow (div_nonneg hM0.le hN0.le) hratio (by linarith : 0 ≤ a - 1)
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg (zero_le_one.trans hT) _),
      ← Real.rpow_mul (zero_le_one.trans hT)] at h
    exact h
  have hMcancel : M ^ (1 - a) * M ^ (a - 1) = 1 := by
    rw [← Real.rpow_add hM0, show 1 - a + (a - 1) = 0 by ring, Real.rpow_zero]
  have hNcombine : N ^ (2 * a - 1) / N ^ (a - 1) = N ^ a := by
    rw [← Real.rpow_sub hN0]
    congr 1
    ring
  have hidentity : V * (M / N) ^ (a - 1) = N ^ a := by
    dsimp [V]
    rw [Real.div_rpow hM0.le hN0.le]
    calc
      _ = (M ^ (1 - a) * M ^ (a - 1)) * (N ^ (2 * a - 1) / N ^ (a - 1)) := by ring
      _ = _ := by rw [hMcancel, hNcombine, one_mul]
  have hNa : N ^ a ≤ ((2 : ℝ) ^ (a - 1) * U) * V := by
    rw [← hidentity]
    simpa only [mul_comm V] using mul_le_mul_of_nonneg_left hpow hV
  have hMU : M ≤ U * M := le_mul_of_one_le_left hM0.le hU
  have htwopos : 0 ≤ (2 : ℝ) ^ (a - 1) := Real.rpow_nonneg (by norm_num) _
  change M + N ^ a ≤ (1 + (2 : ℝ) ^ (a - 1)) * U * (M + N + V)
  nlinarith [mul_nonneg (mul_nonneg htwopos (zero_le_one.trans hU)) hM0.le,
    mul_nonneg (mul_nonneg htwopos (zero_le_one.trans hU)) hN0.le,
    mul_nonneg (zero_le_one.trans hU) hN0.le, mul_nonneg (zero_le_one.trans hU) hV]

end
end ArtinMatthews.QuadraticScale
