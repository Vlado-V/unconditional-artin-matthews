module

public import ArtinMatthews.MarkedProgressionEnvelope


set_option backward.privateInPublic true
@[expose] public section

/-! Fixed powers of log are dominated by the true model truncation and
the actual exponential lower endpoint of each marking band. -/

noncomputable section
namespace ArtinMatthews

open Filter
open scoped Topology

theorem cubicSieve_quarter_floor_le {t δ : ℝ} :
    (1 / 4 : ℝ) ^ ⌊t ^ δ⌋₊ ≤ 4 * Real.exp (-Real.log 4 * t ^ δ) := by
  have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hq : (1 / 4 : ℝ) = Real.exp (-Real.log 4) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    norm_num
  rw [hq, ← Real.exp_nat_mul]
  calc
    _ ≤ Real.exp (Real.log 4 + (-Real.log 4 * t ^ δ)) := by
      apply Real.exp_le_exp.mpr
      have hfloor := Nat.lt_floor_add_one (t ^ δ)
      nlinarith only [mul_le_mul_of_nonneg_right hfloor.le hlog.le]
    _ = _ := by rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4)]

theorem cubicSieve_quarter_floor_log_tendsto {δ : ℝ} (hδ : 0 < δ) (A : ℝ) :
    Tendsto (fun x : ℝ => (Real.log x) ^ A * (1 / 4 : ℝ) ^ ⌊(Real.log x) ^ δ⌋₊)
      atTop (𝓝 0) := by
  have h := ((rpow_mul_exp_neg_rpow_tendsto A hδ
    (Real.log_pos (by norm_num : (1 : ℝ) < 4))).const_mul 4).comp Real.tendsto_log_atTop
  simp only [mul_zero, Function.comp_def] at h
  apply squeeze_zero' _ _ h
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact mul_nonneg (Real.rpow_nonneg (Real.log_pos hx).le A) (pow_nonneg (by norm_num) _)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact (mul_le_mul_of_nonneg_left (cubicSieve_quarter_floor_le (t := Real.log x) (δ := δ))
      (Real.rpow_nonneg (Real.log_pos hx).le A)).trans_eq (by ring)

theorem cubicSieve_marking_lower_log_tendsto {α : ℝ} (hα : 0 < α) (A : ℝ) :
    Tendsto (fun x : ℝ => (Real.log x) ^ A / Real.exp ((Real.log x) ^ α)) atTop (𝓝 0) := by
  have h := (rpow_mul_exp_neg_rpow_tendsto A hα (by norm_num : (0 : ℝ) < 1)).comp Real.tendsto_log_atTop
  simpa only [Function.comp_def, neg_one_mul, Real.exp_neg, div_eq_mul_inv] using h

end ArtinMatthews
