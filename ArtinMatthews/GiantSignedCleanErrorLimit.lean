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

/-! The actual prime lower edge absorbs every fixed logarithmic cost. -/
namespace ArtinMatthews
open Filter
open scoped Topology
noncomputable section

def giantSignedLogErrorEnvelope (B C a x : ℝ) : ℝ :=
  B * (Real.log x) ^ C / Real.exp ((Real.log x) ^ a)

theorem giantSignedLogErrorEnvelope_weighted_tendsto
    (B C A a : ℝ) (ha : 0 < a) :
    Tendsto (fun x : ℝ => (Real.log x) ^ A * giantSignedLogErrorEnvelope B C a x)
      atTop (𝓝 0) := by
  have h := ((rpow_mul_exp_neg_rpow_tendsto (A + C) ha
    (by norm_num : (0 : ℝ) < 1)).comp Real.tendsto_log_atTop).const_mul B
  simp only [Function.comp_def, one_mul, neg_mul, mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [Real.rpow_add (Real.log_pos hx), Real.exp_neg]
  unfold giantSignedLogErrorEnvelope
  ring

theorem giantSignedLogErrorEnvelope_eventually_le
    (B C A a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      giantSignedLogErrorEnvelope B C a x ≤ ε * (Real.log x) ^ (-A) := by
  have hsmall : ∀ᶠ x : ℝ in atTop,
      (Real.log x) ^ A * giantSignedLogErrorEnvelope B C a x ≤ ε :=
    ((tendsto_order.1 (giantSignedLogErrorEnvelope_weighted_tendsto B C A a ha)).2 ε hε).mono
      (fun _ h => h.le)
  filter_upwards [hsmall, eventually_gt_atTop (1 : ℝ)] with x hx hxp
  have hL : 0 < Real.log x := Real.log_pos hxp
  calc
    _ ≤ ε / (Real.log x) ^ A :=
      (le_div_iff₀ (Real.rpow_pos_of_pos hL A)).mpr (by simpa only [mul_comm] using hx)
    _ = _ := by rw [Real.rpow_neg hL.le, div_eq_mul_inv]

end
end ArtinMatthews
