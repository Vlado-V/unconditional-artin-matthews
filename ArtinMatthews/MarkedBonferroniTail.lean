module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! The factorial remainder at logarithmic truncation depth saves every
fixed logarithmic power, as used in the represented-divisor expansion. -/

namespace ArtinMatthews

open Filter
open scoped Asymptotics Topology

noncomputable def markedFactorialTail (C : ℝ) (n : ℕ) : ℝ := C ^ n / n.factorial

theorem markedFactorialTail_nonneg {C : ℝ} (hC : 0 ≤ C) (n : ℕ) :
    0 ≤ markedFactorialTail C n := by
  unfold markedFactorialTail
  positivity

/-- A geometric envelope follows from one term of the exponential series. -/
theorem markedFactorialTail_le_exp {C t : ℝ} (hC : 0 ≤ C) (n : ℕ)
    (ht : t ≤ (n : ℝ)) :
    markedFactorialTail C n ≤ Real.exp (2 * C) * Real.exp (-Real.log 2 * t) := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc
    _ ≤ Real.exp (2 * C) / (2 : ℝ) ^ n := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)).mpr
      calc
        markedFactorialTail C n * 2 ^ n = (2 * C) ^ n / n.factorial := by
          unfold markedFactorialTail
          rw [mul_pow]
          ring
        _ ≤ _ := Real.pow_div_factorial_le_exp (x := 2 * C) (by positivity) n
    _ = Real.exp (2 * C) * Real.exp (-Real.log 2 * (n : ℝ)) := by
      rw [show -Real.log 2 * (n : ℝ) = -((n : ℝ) * Real.log 2) by ring,
        Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_nonneg _)

theorem rpow_mul_exp_neg_rpow_tendsto (A : ℝ) {δ b : ℝ}
    (hδ : 0 < δ) (hb : 0 < b) :
    Tendsto (fun t : ℝ => t ^ A * Real.exp (-b * t ^ δ)) atTop (nhds 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (A / δ) b hb).comp
    (tendsto_rpow_atTop hδ)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  dsimp only [Function.comp_def]
  rw [← Real.rpow_mul ht.le, mul_div_cancel₀ A hδ.ne']

/-- A positive power of the logarithm is enough truncation depth for every
fixed logarithmic saving; no Stirling approximation is assumed. -/
theorem markedFactorialTail_log_depth_tendsto {C δ : ℝ} (hC : 0 ≤ C)
    (hδ : 0 < δ) (A : ℝ) :
    Tendsto (fun x : ℝ => (Real.log x) ^ A *
      markedFactorialTail C (⌊(Real.log x) ^ δ⌋₊ + 1)) atTop (nhds 0) := by
  have hpow : Tendsto (fun t : ℝ => t ^ A *
      markedFactorialTail C (⌊t ^ δ⌋₊ + 1)) atTop (nhds 0) := by
    have hbound := (rpow_mul_exp_neg_rpow_tendsto A hδ
      (Real.log_pos (by norm_num : (1 : ℝ) < 2))).const_mul (Real.exp (2 * C))
    simp only [mul_zero] at hbound
    apply squeeze_zero' _ _ hbound
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      exact mul_nonneg (Real.rpow_nonneg ht.le _) (markedFactorialTail_nonneg hC _)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      have hn : t ^ δ ≤ ((⌊t ^ δ⌋₊ + 1 : ℕ) : ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one (t ^ δ)).le
      have hh := mul_le_mul_of_nonneg_left
        (markedFactorialTail_le_exp hC (⌊t ^ δ⌋₊ + 1) hn) (Real.rpow_nonneg ht.le A)
      convert hh using 1
      ring
  exact hpow.comp Real.tendsto_log_atTop

theorem markedFactorialTail_log_depth_isLittleO {C δ : ℝ} (hC : 0 ≤ C)
    (hδ : 0 < δ) (A : ℝ) :
    (fun x : ℝ => markedFactorialTail C (⌊(Real.log x) ^ δ⌋₊ + 1)) =o[atTop]
      (fun x : ℝ => (Real.log x) ^ (-A)) := by
  apply Asymptotics.isLittleO_of_tendsto' (f := fun x : ℝ =>
    markedFactorialTail C (⌊(Real.log x) ^ δ⌋₊ + 1))
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact fun h => (Real.rpow_pos_of_pos (Real.log_pos hx) (-A)).ne' h |>.elim
  · apply (markedFactorialTail_log_depth_tendsto hC hδ A).congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [Real.rpow_neg (Real.log_pos hx).le, div_inv_eq_mul, mul_comm]

end ArtinMatthews
