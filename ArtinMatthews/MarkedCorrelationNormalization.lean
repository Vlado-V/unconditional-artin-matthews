module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
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


set_option backward.privateInPublic true
@[expose] public section

/-! Converting normalized prime-correlation norm limits to their usual forms. -/

namespace ArtinMatthews

open Filter
open scoped Topology

theorem marked_complex_normalized_tendsto (E : ℝ → ℂ)
    (h : Tendsto (fun x => Real.log x / x * ‖E x‖) atTop (𝓝 0)) :
    Tendsto (fun x => ((Real.log x / x : ℝ) : ℂ) * E x) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (Real.log_pos hx).le (by linarith))]

theorem marked_correlation_isLittleO_of_normalized_norm (E : ℝ → ℂ)
    (h : Tendsto (fun x => Real.log x / x * ‖E x‖) atTop (𝓝 0)) :
    E =o[atTop] (fun x : ℝ => x / Real.log x) := by
  apply Asymptotics.isLittleO_norm_left.mp
  apply Asymptotics.isLittleO_of_tendsto'
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact fun heq => (div_pos (by linarith : 0 < x) (Real.log_pos hx)).ne' heq |>.elim
  · apply h.congr'
    exact Filter.Eventually.of_forall (fun x => by dsimp; rw [div_div_eq_mul_div]; ring)

end ArtinMatthews
