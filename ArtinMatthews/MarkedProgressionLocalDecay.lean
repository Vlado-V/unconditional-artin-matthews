module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import ArtinMatthews.MarkedBonferroniTail
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! The local coprimality loss saves every fixed logarithmic power when
all marking primes exceed an exponential of a positive logarithmic power.
Fixed multiples of the floor depth include the even Bonferroni depth. -/

namespace ArtinMatthews

open Filter
open scoped Asymptotics Topology

/-- A fixed multiple of a floor power, times any real power, is negligible
against an exponential of a positive power. No sign restriction on `δ` is needed. -/
theorem marked_local_loss_scaled_depth_tendsto (δ A : ℝ) (b K : ℕ)
    {α : ℝ} (hα : 0 < α) :
    Tendsto (fun t : ℝ => ((b * ⌊t ^ δ⌋₊ + K : ℕ) : ℝ) * t ^ A /
      Real.exp (t ^ α)) atTop (𝓝 0) := by
  have hfirst := (rpow_mul_exp_neg_rpow_tendsto (δ + A) hα
    (by norm_num : (0 : ℝ) < 1)).const_mul (b : ℝ)
  have hsecond := (rpow_mul_exp_neg_rpow_tendsto A hα
    (by norm_num : (0 : ℝ) < 1)).const_mul (K : ℝ)
  have hbound : Tendsto (fun t : ℝ =>
      (b : ℝ) * (t ^ (δ + A) * Real.exp (-(t ^ α))) +
        (K : ℝ) * (t ^ A * Real.exp (-(t ^ α)))) atTop (𝓝 0) := by
    simpa only [neg_mul, one_mul, mul_zero, zero_add] using hfirst.add hsecond
  apply squeeze_zero' _ _ hbound
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg ht.le A)) (Real.exp_nonneg _)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hk : (⌊t ^ δ⌋₊ : ℝ) ≤ t ^ δ := Nat.floor_le (Real.rpow_nonneg ht.le δ)
    have hcount : ((b * ⌊t ^ δ⌋₊ + K : ℕ) : ℝ) ≤ (b : ℝ) * t ^ δ + K := by
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg b)]
    calc
      _ ≤ ((b : ℝ) * t ^ δ + K) * t ^ A / Real.exp (t ^ α) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcount (Real.rpow_nonneg ht.le A)) (Real.exp_nonneg _)
      _ = _ := by
        simp only [Real.rpow_add ht, Real.exp_neg, div_eq_mul_inv]
        ring

/-- The exact logarithmic local-loss expression tends to zero, including
arbitrary fixed real logarithmic weights. -/
theorem marked_local_loss_scaled_log_depth_tendsto (δ A : ℝ) (b K : ℕ)
    {α : ℝ} (hα : 0 < α) :
    Tendsto (fun x : ℝ => ((b * ⌊(Real.log x) ^ δ⌋₊ + K : ℕ) : ℝ) *
      (Real.log x) ^ A / Real.exp ((Real.log x) ^ α)) atTop (𝓝 0) :=
  (marked_local_loss_scaled_depth_tendsto δ A b K hα).comp Real.tendsto_log_atTop

/-- The originally requested floor depth is the multiplier-one case. -/
theorem marked_local_loss_log_depth_tendsto (δ A : ℝ) (K : ℕ)
    {α : ℝ} (hα : 0 < α) :
    Tendsto (fun x : ℝ => ((⌊(Real.log x) ^ δ⌋₊ + K : ℕ) : ℝ) *
      (Real.log x) ^ A / Real.exp ((Real.log x) ^ α)) atTop (𝓝 0) := by
  simpa only [one_mul] using marked_local_loss_scaled_log_depth_tendsto δ A 1 K hα

/-- The even truncation depth used by the positive Bonferroni remainder. -/
theorem marked_even_local_loss_log_depth_tendsto (δ A : ℝ) (K : ℕ)
    {α : ℝ} (hα : 0 < α) :
    Tendsto (fun x : ℝ => ((2 * ⌊(Real.log x) ^ δ⌋₊ + K : ℕ) : ℝ) *
      (Real.log x) ^ A / Real.exp ((Real.log x) ^ α)) atTop (𝓝 0) :=
  marked_local_loss_scaled_log_depth_tendsto δ A 2 K hα

/-- The same estimate as a saving of every prescribed logarithmic power. -/
theorem marked_local_loss_scaled_log_depth_isLittleO (δ A : ℝ) (b K : ℕ)
    {α : ℝ} (hα : 0 < α) :
    (fun x : ℝ => ((b * ⌊(Real.log x) ^ δ⌋₊ + K : ℕ) : ℝ) /
      Real.exp ((Real.log x) ^ α)) =o[atTop] (fun x => (Real.log x) ^ (-A)) := by
  apply Asymptotics.isLittleO_of_tendsto'
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact fun h => (Real.rpow_pos_of_pos (Real.log_pos hx) (-A)).ne' h |>.elim
  · apply (marked_local_loss_scaled_log_depth_tendsto δ A b K hα).congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [Real.rpow_neg (Real.log_pos hx).le, div_inv_eq_mul]
    ring

end ArtinMatthews
