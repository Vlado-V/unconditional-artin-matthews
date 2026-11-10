module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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

/-! The actual polynomially enlarged frequency height has logarithm
bounded by a fixed multiple of `log x`; no height-growth assumption is
needed when specializing the sparse-sample estimate. -/

namespace ArtinMatthews

open Filter

/-- Any fixed nonnegative logarithmic enlargement is absorbed by a second
copy of `log x`. The explicit factor four matches the major-arc height. -/
theorem marked_sparse_frequency_height (B : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ x : ℝ in atTop,
      1 < 4*x*(Real.log x)^B ∧
      Real.log (4*x*(Real.log x)^B) ≤ 2*Real.log x := by
  have hε : 0 < 1/(2*(B+1)) := by positivity
  have hb := (isLittleO_log_rpow_atTop (show (0:ℝ) < 1 by norm_num)).bound hε
  filter_upwards [Real.tendsto_log_atTop.eventually hb,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (6:ℝ)),
    eventually_gt_atTop (1:ℝ)] with x hb hL hx
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := by linarith
  have hLL : 0 ≤ Real.log (Real.log x) := Real.log_nonneg (by linarith)
  rw [Real.norm_eq_abs,abs_of_nonneg hLL,Real.rpow_one,
    Real.norm_eq_abs,abs_of_pos hlog] at hb
  have hBsmall : B * Real.log (Real.log x) ≤ Real.log x / 2 := by
    have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2*(B+1) by positivity)
    have he : (2*(B+1)) * (1/(2*(B+1)) * Real.log x) = Real.log x := by
      field_simp
    rw [he] at hh
    nlinarith
  have hpow : 1 ≤ (Real.log x)^B := Real.one_le_rpow (by linarith) hB
  have hpow0 : 0 < (Real.log x)^B := Real.rpow_pos_of_pos hlog _
  constructor
  · have hh := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 4*x by positivity)
    nlinarith
  · rw [Real.log_mul (by positivity : (4*x) ≠ 0) hpow0.ne',
      Real.log_mul (by norm_num : (4:ℝ) ≠ 0) hx0.ne',Real.log_rpow hlog]
    have h4 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4)
    nlinarith

end ArtinMatthews
