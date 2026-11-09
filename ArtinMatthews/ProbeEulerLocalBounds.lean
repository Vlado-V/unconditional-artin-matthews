module

public import ArtinMatthews.ProbeEulerLocalAlgebra


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

noncomputable section

theorem probe_one_sub_norm_upper {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖1 - z‖ ≤ 2 := by
  have h := norm_sub_le (1 : ℂ) z
  norm_num at h
  linarith

theorem probeGoodLocalErrorNumerator_norm_le (Q V W D : ℂ)
    (hQ : 1 ≤ ‖Q‖) (hV : ‖V‖ ≤ 1 / 2) (hW : ‖W‖ ≤ 1 / 2) :
    ‖probeGoodLocalErrorNumerator Q V W D‖ ≤
      4 * (‖D‖ * ‖W‖ + ‖D‖ * ‖V‖ + ‖W‖ * ‖V‖ +
        ‖Q‖ * ‖D‖ * ‖W‖ * ‖V‖) := by
  have hsum : ‖W + V - W * V‖ ≤ 2 * (‖W‖ + ‖V‖) := by
    have h := norm_sub_le (W + V) (W * V)
    have ha := norm_add_le W V
    rw [norm_mul] at h
    have hp : ‖W‖ * ‖V‖ ≤ ‖W‖ :=
      mul_le_of_le_one_right (norm_nonneg _) (by linarith)
    linarith [norm_nonneg V]
  have hqm : ‖Q - 1‖ ≤ 2 * ‖Q‖ := by
    have h := norm_sub_le Q (1 : ℂ)
    norm_num at h
    linarith
  have htail : ‖(Q - 1) * D * (1 - W) * W * V‖ ≤
      4 * ‖Q‖ * ‖D‖ * ‖W‖ * ‖V‖ := by
    simp only [norm_mul]
    calc
      _ ≤ (2 * ‖Q‖) * ‖D‖ * 2 * ‖W‖ * ‖V‖ := by
        gcongr
        exact probe_one_sub_norm_upper hW
      _ = _ := by ring
  have hfirst : ‖D * (W + V - W * V)‖ ≤
      2 * (‖D‖ * ‖W‖ + ‖D‖ * ‖V‖) := by
    rw [norm_mul]
    calc
      _ ≤ ‖D‖ * (2 * (‖W‖ + ‖V‖)) := by gcongr
      _ = _ := by ring
  have ha := norm_sub_le (D * (W + V - W * V)) (W * V)
  have hb := norm_sub_le (D * (W + V - W * V) - W * V)
    ((Q - 1) * D * (1 - W) * W * V)
  rw [norm_mul W V] at ha
  unfold probeGoodLocalErrorNumerator
  nlinarith [mul_nonneg (norm_nonneg D) (norm_nonneg W),
    mul_nonneg (norm_nonneg D) (norm_nonneg V),
    mul_nonneg (norm_nonneg W) (norm_nonneg V)]

theorem probeGoodLocalGeometricNumerator_norm_le (Q V W D : ℂ)
    (hQ : 1 ≤ ‖Q‖) (hV : ‖V‖ ≤ 1 / 2) (hW : ‖W‖ ≤ 1 / 2)
    (hD : ‖D‖ ≤ 1 / 2) :
    ‖probeGoodLocalGeometricNumerator Q V W D‖ ≤ 6 := by
  have hqi : ‖Q⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hQ
  have hw2 : ‖W‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (by linarith)
  have hterm : ‖(1 - W) * Q⁻¹‖ ≤ 2 := by
    rw [norm_mul]
    calc
      _ ≤ 2 * 1 := mul_le_mul (probe_one_sub_norm_upper hW) hqi
        (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hlast : ‖W ^ 2 * (1 - V)‖ ≤ 2 := by
    rw [norm_mul, norm_pow]
    calc
      _ ≤ 1 * 2 := mul_le_mul hw2 (probe_one_sub_norm_upper hV)
        (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have ha := norm_sub_le (1 - D) ((1 - W) * Q⁻¹)
  have hb := norm_sub_le ((1 - D) - (1 - W) * Q⁻¹) (W ^ 2 * (1 - V))
  have hd := probe_one_sub_norm_upper hD
  unfold probeGoodLocalGeometricNumerator
  linarith

theorem probeGoodLocalCorrection_norm_sub_one_le (Q V W D E : ℂ)
    (hQ : 1 ≤ ‖Q‖) (hV : ‖V‖ ≤ 1 / 2) (hW : ‖W‖ ≤ 1 / 2)
    (hD : ‖D‖ ≤ 1 / 2) (hE : ‖E‖ ≤ 1 / 2) :
    ‖probeGoodLocalCorrection Q V W D E - 1‖ ≤
      32 * (‖D‖ * ‖W‖ + ‖D‖ * ‖V‖ + ‖W‖ * ‖V‖ +
        ‖Q‖ * ‖D‖ * ‖W‖ * ‖V‖ + ‖E‖) := by
  have hQ0 : Q ≠ 0 := norm_pos_iff.mp (by linarith)
  rw [probeGoodLocalCorrection_sub_one Q V W D E hQ0
    (probe_one_sub_ne_zero hV) (probe_one_sub_ne_zero hW)
    (probe_one_sub_ne_zero hD) (probe_one_sub_ne_zero hE), norm_div, norm_mul]
  let S := ‖D‖ * ‖W‖ + ‖D‖ * ‖V‖ + ‖W‖ * ‖V‖ +
    ‖Q‖ * ‖D‖ * ‖W‖ * ‖V‖
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have ha : ‖probeGoodLocalErrorNumerator Q V W D‖ ≤ 4 * S :=
    probeGoodLocalErrorNumerator_norm_le Q V W D hQ hV hW
  have hb := probeGoodLocalGeometricNumerator_norm_le Q V W D hQ hV hW hD
  have hn : ‖probeGoodLocalErrorNumerator Q V W D +
      E * probeGoodLocalGeometricNumerator Q V W D‖ ≤ 8 * (S + ‖E‖) := by
    have ht : ‖E * probeGoodLocalGeometricNumerator Q V W D‖ ≤ ‖E‖ * 6 := by
      rw [norm_mul]
      gcongr
    have hs := norm_add_le (probeGoodLocalErrorNumerator Q V W D)
      (E * probeGoodLocalGeometricNumerator Q V W D)
    linarith [norm_nonneg E]
  have hden : 1 / 4 ≤ ‖1 - D‖ * ‖1 - E‖ := by
    have h := mul_le_mul (probe_one_sub_norm_lower hD)
      (probe_one_sub_norm_lower hE) (by norm_num : (0 : ℝ) ≤ 1 / 2) (norm_nonneg _)
    norm_num at h ⊢
    exact h
  apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num) hden)).mpr
  change _ ≤ 32 * (S + ‖E‖) * _
  calc
    _ ≤ 8 * (S + ‖E‖) := hn
    _ ≤ 32 * (S + ‖E‖) * (‖1 - D‖ * ‖1 - E‖) := by
      have h := mul_le_mul_of_nonneg_left hden (by positivity : 0 ≤ 32 * (S + ‖E‖))
      nlinarith

end

end ArtinMatthews
