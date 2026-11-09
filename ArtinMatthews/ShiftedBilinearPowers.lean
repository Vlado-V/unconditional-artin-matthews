module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring


set_option backward.privateInPublic true
@[expose] public section

/-! Exact scalar comparisons and square-budget extraction for the shifted bilinear bound. -/
namespace ArtinMatthews
noncomputable section

theorem shiftedBilinear_highRegion_power (M T : ℝ) (hM : 1 ≤ M) (hT : 1 ≤ T)
    (hregion : M ^ 2 ≤ T) :
    M ^ 3 * T ^ (3 / 2 : ℝ) ≤ M ^ (5 / 2 : ℝ) * T ^ (7 / 4 : ℝ) := by
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM
  have hT0 : 0 ≤ T := le_trans (by norm_num) hT
  have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hTp : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hroot : M ^ (1 / 2 : ℝ) ≤ T ^ (1 / 4 : ℝ) := by
    have h := Real.rpow_le_rpow (sq_nonneg M) hregion (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rw [← Real.rpow_natCast M 2, ← Real.rpow_mul hM0] at h
    norm_num at h ⊢
    exact h
  have hMsplit : M ^ (5 / 2 : ℝ) * M ^ (1 / 2 : ℝ) = M ^ 3 := by
    rw [← Real.rpow_add hMp]
    norm_num
  have hTsplit : T ^ (3 / 2 : ℝ) * T ^ (1 / 4 : ℝ) = T ^ (7 / 4 : ℝ) := by
    rw [← Real.rpow_add hTp]
    norm_num
  calc
    M ^ 3 * T ^ (3 / 2 : ℝ) =
        (M ^ (5 / 2 : ℝ) * T ^ (3 / 2 : ℝ)) * M ^ (1 / 2 : ℝ) := by
      rw [← hMsplit]
      ring
    _ ≤ (M ^ (5 / 2 : ℝ) * T ^ (3 / 2 : ℝ)) * T ^ (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left hroot
        (mul_nonneg (Real.rpow_nonneg hM0 _) (Real.rpow_nonneg hT0 _))
    _ = M ^ (5 / 2 : ℝ) * T ^ (7 / 4 : ℝ) := by rw [← hTsplit]; ring

theorem shiftedBilinear_lowRegion_power (M T : ℝ) (hM : 1 ≤ M) (hT : 1 ≤ T)
    (hregion : T ≤ M ^ 2) :
    M * T ≤ M ^ (5 / 4 : ℝ) * T ^ (7 / 8 : ℝ) := by
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM
  have hT0 : 0 ≤ T := le_trans (by norm_num) hT
  have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hTp : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hroot : T ^ (1 / 8 : ℝ) ≤ M ^ (1 / 4 : ℝ) := by
    have h := Real.rpow_le_rpow hT0 hregion (by norm_num : (0 : ℝ) ≤ 1 / 8)
    rw [← Real.rpow_natCast M 2, ← Real.rpow_mul hM0] at h
    norm_num at h ⊢
    exact h
  have hMsplit : M * M ^ (1 / 4 : ℝ) = M ^ (5 / 4 : ℝ) := by
    have h := (Real.rpow_add hMp (1 : ℝ) (1 / 4 : ℝ)).symm
    norm_num at h
    exact h
  have hTsplit : T ^ (7 / 8 : ℝ) * T ^ (1 / 8 : ℝ) = T := by
    rw [← Real.rpow_add hTp]
    norm_num
  calc
    M * T = (M * T ^ (7 / 8 : ℝ)) * T ^ (1 / 8 : ℝ) := by rw [mul_assoc, hTsplit]
    _ ≤ (M * T ^ (7 / 8 : ℝ)) * M ^ (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left hroot (mul_nonneg hM0 (Real.rpow_nonneg hT0 _))
    _ = M ^ (5 / 4 : ℝ) * T ^ (7 / 8 : ℝ) := by rw [← hMsplit]; ring

theorem shiftedBilinear_squaredBudget (M T S C E δ : ℝ)
    (hM : 1 ≤ M) (hT : 1 ≤ T) (hS : 0 ≤ S) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hCS : S ^ 2 ≤ T * E)
    (hbudget : E ≤ C * (M * T) ^ δ *
      (M * T + M ^ 3 * T ^ (1 / 2 : ℝ) + M ^ (5 / 2 : ℝ) * T ^ (3 / 4 : ℝ)))
    (hregion : M ^ 2 ≤ T) :
    S ≤ Real.sqrt (2 * C) * (M * T) ^ (δ / 2) *
      (Real.sqrt M * T + M ^ (5 / 4 : ℝ) * T ^ (7 / 8 : ℝ)) := by
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM
  have hT0 : 0 ≤ T := le_trans (by norm_num) hT
  have hTp : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hMT0 : 0 ≤ M * T := mul_nonneg hM0 hT0
  let A := Real.sqrt M * T
  let B := M ^ (5 / 4 : ℝ) * T ^ (7 / 8 : ℝ)
  have hA0 : 0 ≤ A := mul_nonneg (Real.sqrt_nonneg _) hT0
  have hB0 : 0 ≤ B := mul_nonneg (Real.rpow_nonneg hM0 _) (Real.rpow_nonneg hT0 _)
  have hA2 : A ^ 2 = M * T ^ 2 := by
    dsimp [A]
    rw [mul_pow, Real.sq_sqrt hM0]
  have hB2 : B ^ 2 = M ^ (5 / 2 : ℝ) * T ^ (7 / 4 : ℝ) := by
    dsimp [B]
    rw [mul_pow, ← Real.rpow_two, ← Real.rpow_two,
      ← Real.rpow_mul hM0, ← Real.rpow_mul hT0]
    norm_num
  have hhalf : T * T ^ (1 / 2 : ℝ) = T ^ (3 / 2 : ℝ) := by
    have h := (Real.rpow_add hTp (1 : ℝ) (1 / 2 : ℝ)).symm
    norm_num at h
    exact h
  have hthree : T * T ^ (3 / 4 : ℝ) = T ^ (7 / 4 : ℝ) := by
    have h := (Real.rpow_add hTp (1 : ℝ) (3 / 4 : ℝ)).symm
    norm_num at h
    exact h
  have hterms : T * (M * T + M ^ 3 * T ^ (1 / 2 : ℝ) +
      M ^ (5 / 2 : ℝ) * T ^ (3 / 4 : ℝ)) ≤ 2 * (A + B) ^ 2 := by
    calc
      _ = M * T ^ 2 + M ^ 3 * T ^ (3 / 2 : ℝ) +
          M ^ (5 / 2 : ℝ) * T ^ (7 / 4 : ℝ) := by
        rw [← hhalf, ← hthree]
        ring
      _ ≤ M * T ^ 2 + 2 * (M ^ (5 / 2 : ℝ) * T ^ (7 / 4 : ℝ)) := by
        have h := shiftedBilinear_highRegion_power M T hM hT hregion
        linarith
      _ = A ^ 2 + 2 * B ^ 2 := by rw [hA2, hB2]
      _ ≤ 2 * (A + B) ^ 2 := by nlinarith [mul_nonneg hA0 hB0, sq_nonneg A]
  have hbound : S ^ 2 ≤ 2 * C * (M * T) ^ δ * (A + B) ^ 2 := by
    calc
      S ^ 2 ≤ T * E := hCS
      _ ≤ T * (C * (M * T) ^ δ * (M * T + M ^ 3 * T ^ (1 / 2 : ℝ) +
          M ^ (5 / 2 : ℝ) * T ^ (3 / 4 : ℝ))) := mul_le_mul_of_nonneg_left hbudget hT0
      _ = (C * (M * T) ^ δ) * (T * (M * T + M ^ 3 * T ^ (1 / 2 : ℝ) +
          M ^ (5 / 2 : ℝ) * T ^ (3 / 4 : ℝ))) := by ring
      _ ≤ (C * (M * T) ^ δ) * (2 * (A + B) ^ 2) :=
        mul_le_mul_of_nonneg_left hterms (mul_nonneg hC (Real.rpow_nonneg hMT0 _))
      _ = 2 * C * (M * T) ^ δ * (A + B) ^ 2 := by ring
  have hpow : ((M * T) ^ (δ / 2)) ^ 2 = (M * T) ^ δ := by
    rw [← Real.rpow_two, ← Real.rpow_mul hMT0]
    congr 1
    ring
  have htarget0 : 0 ≤ Real.sqrt (2 * C) * (M * T) ^ (δ / 2) * (A + B) :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hMT0 _)) (add_nonneg hA0 hB0)
  have htarget2 : (Real.sqrt (2 * C) * (M * T) ^ (δ / 2) * (A + B)) ^ 2 =
      2 * C * (M * T) ^ δ * (A + B) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg (by norm_num) hC), hpow]
  change S ≤ Real.sqrt (2 * C) * (M * T) ^ (δ / 2) * (A + B)
  exact (sq_le_sq₀ hS htarget0).mp (hbound.trans_eq htarget2.symm)

end
end ArtinMatthews
