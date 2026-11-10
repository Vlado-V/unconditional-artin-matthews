module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! The actual polynomial detector height lies in the original source
subexponential height range. -/
namespace ArtinMatthews
open Filter

theorem markedPhysicalTypeII_log_height (Qexp B : ℝ) (hB : 0 < B) :
    ∀ᶠ x : ℝ in atTop,(Real.log x)^Qexp ≤ Real.exp (B*(Real.log x)^(1/5:ℝ)) := by
  have hr : Tendsto (fun L : ℝ => Qexp*(Real.log L/L^(1/5:ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using
      ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/5)).tendsto_div_nhds_zero).const_mul Qexp
  filter_upwards [Real.tendsto_log_atTop.eventually (hr.eventually (Iio_mem_nhds hB)),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0:ℝ))] with x hx hL
  have hratio : (Qexp*Real.log (Real.log x))/(Real.log x)^(1/5:ℝ) < B := by
    simpa only [div_eq_mul_inv,mul_assoc] using hx
  have hp := (div_lt_iff₀ (Real.rpow_pos_of_pos hL (1/5:ℝ))).mp hratio
  rw [Real.rpow_def_of_pos hL]
  exact Real.exp_le_exp.mpr (by nlinarith)

end ArtinMatthews
