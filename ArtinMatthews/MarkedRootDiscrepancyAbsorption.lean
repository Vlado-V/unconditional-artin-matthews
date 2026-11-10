module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import ArtinMatthews.MarkedProgressionGrowth
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
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


set_option backward.privateInPublic true
@[expose] public section

/-! A proved power saving absorbs the actual subpower coefficient counts
from the finite root-arc expansion. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped Asymptotics Topology

theorem marked_root_power_isLittleO_log {b : ℝ} (hb : 0 < b) (A : ℝ) :
    (fun x : ℝ => x^(-b)) =o[atTop] (fun x : ℝ => (Real.log x)^(-A)) := by
  have h := (isLittleO_log_rpow_rpow_atTop A hb).inv_rev (by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact fun hz => ((Real.rpow_pos_of_pos (Real.log_pos hx) A).ne' hz).elim)
  apply h.congr' _ _
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact (Real.rpow_neg (by linarith : 0 ≤ x) b).symm
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact (Real.rpow_neg (Real.log_pos hx).le A).symm

theorem marked_root_subpower_error_isLittleO (E C a b A : ℝ) (ha : a < 1) (hb : 0 < b) :
    (fun x : ℝ => E*Real.exp (C*(Real.log x)^a)*x^(-b)) =o[atTop]
      (fun x : ℝ => (Real.log x)^(-A)) := by
  have hg : (fun x : ℝ => E*Real.exp (C*(Real.log x)^a)*x^(-b)) =O[atTop]
      (fun x : ℝ => x^(-(b/2))) := by
    apply Asymptotics.IsBigO.of_bound |E|
    filter_upwards [marked_sublinear_log_exp_le_rpow_eventually a C (b/2) ha (by positivity),
      eventually_gt_atTop (0 : ℝ)] with x hx hx0
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _),
      abs_of_pos (Real.exp_pos _)]
    apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx (abs_nonneg E))
      (Real.rpow_nonneg hx0.le _)).trans_eq
    rw [mul_assoc, ← Real.rpow_add hx0]
    congr 2
    ring
  exact hg.trans_isLittleO (marked_root_power_isLittleO_log (by positivity : 0 < b/2) A)

end ArtinMatthews
