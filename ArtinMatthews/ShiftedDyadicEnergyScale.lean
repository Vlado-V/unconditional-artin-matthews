module

public import ArtinMatthews.ShiftedBilinearPowers
public import Mathlib.Tactic.GCongr


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform conversion of the actual weighted-energy scale to the dyadic scale. -/
namespace ArtinMatthews
noncomputable section

theorem shiftedDyadic_energyScale (M T S ε C K : ℝ)
    (hM : 1 ≤ M) (hT : 1 ≤ T) (hS : 1 ≤ S) (hST : S ≤ 2 * T)
    (hε : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2) (hC : 0 ≤ C) (hK : 0 ≤ K) :
    K * (6 * M * S + 1) ^ (1 + ε) +
      C * K * (M * S) ^ ε * (2 * M) ^ (2 + ε) *
        (Real.sqrt (M * S + 1) * Real.sqrt M +
          (M * S + 1) ^ (3 / 4 : ℝ) / M ^ (1 / 4 : ℝ)) ≤
      (169 * K + 64 * C * K) * (M * T) ^ (2 * ε) *
        (M * T + M ^ 3 * T ^ (1 / 2 : ℝ) + M ^ (5 / 2 : ℝ) * T ^ (3 / 4 : ℝ)) := by
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM
  have hT0 : 0 ≤ T := le_trans (by norm_num) hT
  have hS0 : 0 ≤ S := le_trans (by norm_num) hS
  have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
  let R := M * T
  have hR1 : 1 ≤ R := by dsimp [R]; nlinarith
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR1
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hMS0 : 0 ≤ M * S := mul_nonneg hM0 hS0
  have hMS : M * S ≤ 2 * R := by
    have h := mul_le_mul_of_nonneg_left hST hM0
    dsimp [R]
    nlinarith
  have hDarg : 6 * M * S + 1 ≤ 13 * R := by nlinarith
  have harg : M * S + 1 ≤ 4 * R := by nlinarith
  have h13 : (13 : ℝ) ^ (1 + ε) ≤ 169 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 13)
      (show 1 + ε ≤ 2 by linarith)
    norm_num at h
    exact h
  have hD : (6 * M * S + 1) ^ (1 + ε) ≤ 169 * R ^ (2 * ε) * R := by
    calc
      _ ≤ (13 * R) ^ (1 + ε) := Real.rpow_le_rpow (by positivity) hDarg (by linarith)
      _ = (13 : ℝ) ^ (1 + ε) * R ^ (1 + ε) := Real.mul_rpow (by norm_num) hR0
      _ ≤ 169 * R ^ (1 + 2 * ε) :=
        mul_le_mul h13 (Real.rpow_le_rpow_of_exponent_le hR1 (by linarith))
          (Real.rpow_nonneg hR0 _) (by norm_num)
      _ = 169 * R ^ (2 * ε) * R := by rw [Real.rpow_add hRp, Real.rpow_one]; ring
  have h2 : (2 : ℝ) ^ ε ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (show ε ≤ 1 by linarith)
  have hP : (M * S) ^ ε ≤ 2 * R ^ ε := by
    calc
      _ ≤ (2 * R) ^ ε := Real.rpow_le_rpow hMS0 hMS hε
      _ = (2 : ℝ) ^ ε * R ^ ε := Real.mul_rpow (by norm_num) hR0
      _ ≤ 2 * R ^ ε := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hR0 _)
  have h8 : (2 : ℝ) ^ (2 + ε) ≤ 8 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show 2 + ε ≤ 3 by linarith)
    norm_num at h
    exact h
  have hMR : M ≤ R := by dsimp [R]; nlinarith
  have hQ : (2 * M) ^ (2 + ε) ≤ 8 * M ^ 2 * R ^ ε := by
    calc
      _ = (2 : ℝ) ^ (2 + ε) * (M ^ 2 * M ^ ε) := by
        rw [Real.mul_rpow (by norm_num) hM0, Real.rpow_add hMp, Real.rpow_two]
      _ ≤ 8 * (M ^ 2 * R ^ ε) := by
        apply mul_le_mul h8
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hM0 hMR hε) (sq_nonneg M))
          (mul_nonneg (sq_nonneg M) (Real.rpow_nonneg hM0 _)) (by norm_num)
      _ = _ := by ring
  have hRoots : Real.sqrt R * Real.sqrt M = M * Real.sqrt T := by
    dsimp [R]
    rw [Real.sqrt_mul hM0]
    calc
      (Real.sqrt M * Real.sqrt T) * Real.sqrt M = (Real.sqrt M) ^ 2 * Real.sqrt T := by ring
      _ = M * Real.sqrt T := by rw [Real.sq_sqrt hM0]
  have hRoot4 : Real.sqrt (4 * R) = 2 * Real.sqrt R := by
    have hfour : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hfour]
  have hFirst : Real.sqrt (M * S + 1) * Real.sqrt M ≤ 4 * M * T ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ Real.sqrt (4 * R) * Real.sqrt M :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt harg) (Real.sqrt_nonneg _)
      _ = 2 * M * Real.sqrt T := by rw [hRoot4]; rw [mul_assoc, hRoots]; ring
      _ ≤ 4 * M * Real.sqrt T := by nlinarith [mul_nonneg hM0 (Real.sqrt_nonneg T)]
      _ = _ := by rw [Real.sqrt_eq_rpow]
  have hQuarter : 0 < M ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hMp _
  have hRdiv : R ^ (3 / 4 : ℝ) / M ^ (1 / 4 : ℝ) = M ^ (1 / 2 : ℝ) * T ^ (3 / 4 : ℝ) := by
    dsimp [R]
    rw [Real.mul_rpow hM0 hT0]
    calc
      _ = (M ^ (3 / 4 : ℝ) / M ^ (1 / 4 : ℝ)) * T ^ (3 / 4 : ℝ) := by ring
      _ = _ := by rw [← Real.rpow_sub hMp]; norm_num
  have h4 : (4 : ℝ) ^ (3 / 4 : ℝ) ≤ 4 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
        (by norm_num : (3 / 4 : ℝ) ≤ 1)
  have hSecond : (M * S + 1) ^ (3 / 4 : ℝ) / M ^ (1 / 4 : ℝ) ≤
      4 * M ^ (1 / 2 : ℝ) * T ^ (3 / 4 : ℝ) := by
    calc
      _ ≤ (4 * R) ^ (3 / 4 : ℝ) / M ^ (1 / 4 : ℝ) :=
        div_le_div_of_nonneg_right (Real.rpow_le_rpow (by positivity) harg (by norm_num)) hQuarter.le
      _ = (4 : ℝ) ^ (3 / 4 : ℝ) * (R ^ (3 / 4 : ℝ) / M ^ (1 / 4 : ℝ)) := by
        rw [Real.mul_rpow (by norm_num) hR0]
        ring
      _ ≤ 4 * (R ^ (3 / 4 : ℝ) / M ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_right h4 (div_nonneg (Real.rpow_nonneg hR0 _) hQuarter.le)
      _ = _ := by rw [hRdiv]; ring
  have hBracket : Real.sqrt (M * S + 1) * Real.sqrt M +
      (M * S + 1) ^ (3 / 4 : ℝ) / M ^ (1 / 4 : ℝ) ≤
      4 * (M * T ^ (1 / 2 : ℝ) + M ^ (1 / 2 : ℝ) * T ^ (3 / 4 : ℝ)) := by linarith
  have hRmul : R ^ ε * R ^ ε = R ^ (2 * ε) := by
    rw [← Real.rpow_add hRp]
    congr 1
    ring
  have hMmul : M ^ 2 * M ^ (1 / 2 : ℝ) = M ^ (5 / 2 : ℝ) := by
    rw [← Real.rpow_natCast M 2, ← Real.rpow_add hMp]
    norm_num
  have hExpand : M ^ 2 * (M * T ^ (1 / 2 : ℝ) + M ^ (1 / 2 : ℝ) * T ^ (3 / 4 : ℝ)) =
      M ^ 3 * T ^ (1 / 2 : ℝ) + M ^ (5 / 2 : ℝ) * T ^ (3 / 4 : ℝ) := by
    calc
      _ = M ^ 3 * T ^ (1 / 2 : ℝ) + (M ^ 2 * M ^ (1 / 2 : ℝ)) * T ^ (3 / 4 : ℝ) := by ring
      _ = _ := by rw [hMmul]
  have hOff : C * K * (M * S) ^ ε * (2 * M) ^ (2 + ε) *
      (Real.sqrt (M * S + 1) * Real.sqrt M + (M * S + 1) ^ (3 / 4 : ℝ) / M ^ (1 / 4 : ℝ)) ≤
      64 * C * K * R ^ (2 * ε) *
        (M ^ 3 * T ^ (1 / 2 : ℝ) + M ^ (5 / 2 : ℝ) * T ^ (3 / 4 : ℝ)) := by
    calc
      _ ≤ C * K * (2 * R ^ ε) * (8 * M ^ 2 * R ^ ε) *
          (4 * (M * T ^ (1 / 2 : ℝ) + M ^ (1 / 2 : ℝ) * T ^ (3 / 4 : ℝ))) := by
        gcongr
      _ = 64 * C * K * (R ^ ε * R ^ ε) *
          (M ^ 2 * (M * T ^ (1 / 2 : ℝ) + M ^ (1 / 2 : ℝ) * T ^ (3 / 4 : ℝ))) := by ring
      _ = _ := by rw [hRmul, hExpand]
  have hU0 : 0 ≤ M ^ 3 * T ^ (1 / 2 : ℝ) + M ^ (5 / 2 : ℝ) * T ^ (3 / 4 : ℝ) := by positivity
  have hScalar : 169 * K * R + 64 * C * K *
      (M ^ 3 * T ^ (1 / 2 : ℝ) + M ^ (5 / 2 : ℝ) * T ^ (3 / 4 : ℝ)) ≤
      (169 * K + 64 * C * K) *
        (R + M ^ 3 * T ^ (1 / 2 : ℝ) + M ^ (5 / 2 : ℝ) * T ^ (3 / 4 : ℝ)) := by
    nlinarith [mul_nonneg (show 0 ≤ 169 * K by positivity) hU0,
      mul_nonneg (show 0 ≤ 64 * C * K by positivity) hR0]
  calc
    _ ≤ K * (169 * R ^ (2 * ε) * R) + 64 * C * K * R ^ (2 * ε) *
        (M ^ 3 * T ^ (1 / 2 : ℝ) + M ^ (5 / 2 : ℝ) * T ^ (3 / 4 : ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left hD hK) hOff
    _ = R ^ (2 * ε) * (169 * K * R + 64 * C * K *
        (M ^ 3 * T ^ (1 / 2 : ℝ) + M ^ (5 / 2 : ℝ) * T ^ (3 / 4 : ℝ))) := by ring
    _ ≤ R ^ (2 * ε) * ((169 * K + 64 * C * K) *
        (R + M ^ 3 * T ^ (1 / 2 : ℝ) + M ^ (5 / 2 : ℝ) * T ^ (3 / 4 : ℝ))) :=
      mul_le_mul_of_nonneg_left hScalar (Real.rpow_nonneg hR0 _)
    _ = _ := by dsimp [R]; ring

end
end ArtinMatthews
