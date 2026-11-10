module

public import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMovingGrowth
public import ArtinMatthews.MarkedMajorArcScale
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.NumberTheory.Chebyshev
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
public import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMovingGrowthWindow


set_option backward.privateInPublic true
@[expose] public section

/-! Full polynomial-height and arbitrary fixed polylogarithmic-conductor
bookkeeping for the genuine Hurwitz-derived zero-free strip. -/
namespace ArtinMatthews

open Filter OAI.TwoPointCorrelations
open scoped Topology

lemma marked_major_arc_log_height {b L t : ℝ}
    (hb : 0 ≤ b) (hL : 0 ≤ L) (hL5 : Real.log 5 ≤ L)
    (ht : |t| ≤ Real.exp (b*L)) :
    mrtVKLog (2*t) ≤ (b+1)*L := by
  have hE : 1 ≤ Real.exp (b*L) := Real.one_le_exp_iff.mpr (mul_nonneg hb hL)
  have hh : |2*t|+3 ≤ 5*Real.exp (b*L) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith
  have hl := Real.log_le_log (by positivity : (0:ℝ) < |2*t|+3) hh
  rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp] at hl
  change Real.log (|2*t|+3) ≤ _
  linarith

lemma marked_major_arc_weight {C b L t : ℝ} {q : ℕ} [NeZero q]
    (hb : 0 ≤ b) (hL : 0 < L) (hlog : 1 ≤ Real.log L)
    (hq : (q:ℝ) ≤ L^C) (hH : mrtVKLog (2*t) ≤ (b+1)*L) :
    mrtVKWeight q (2*t) ≤ (C+b+2)*Real.log L := by
  have hq0 : (0:ℝ)<q := by exact_mod_cast NeZero.pos q
  have hlogq := Real.log_le_log hq0 hq
  rw [Real.log_rpow hL] at hlogq
  have hlogH := Real.log_le_log (mrt_VKLog_pos (2*t)) hH
  have hb1 : 0 < b+1 := by linarith
  rw [Real.log_mul hb1.ne' hL.ne'] at hlogH
  have hlogb := Real.log_le_sub_one_of_pos hb1
  have hmul := mul_le_mul_of_nonneg_left hlog (by linarith : 0 ≤ b+1)
  unfold mrtVKWeight
  nlinarith

/-- The same rectangle works for every modulus below an arbitrary fixed
power of the logarithmic scale, and every frequency up to `exp (b*L)`. -/
theorem marked_major_arc_character_budget (C b c : ℝ)
    (hC : 0 ≤ C) (hb : 0 ≤ b) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ (q : ℕ) [NeZero q], (q:ℝ) ≤ L^C →
      ∀ t : ℝ, |t| ≤ Real.exp (b*L) →
      L^(-(3/4:ℝ)) ≤ c*mrtVKRadius (2*t)/mrtVKWeight q (2*t) ∧
      (mrtVKWeight q (2*t))^2*(mrtVKLog (2*t))^(2/3:ℝ) ≤ L^2 ∧
      1/L ≤ mrtVKRadius (2*t)/16 := by
  filter_upwards [marked_major_arc_rectangle_budget (C+b+2) (b+1) c
    (by linarith) (by linarith) hc,
    eventually_ge_atTop (Real.exp 1), eventually_ge_atTop (Real.log 5)]
    with L hbudget hLe hL5
  intro q _ hq t ht
  have hL0 : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hL0).mpr hLe
  have hH1 : 1 ≤ mrtVKLog (2*t) := by
    apply (Real.le_log_iff_exp_le (by positivity : (0:ℝ) < |2*t|+3)).mpr
    linarith [Real.exp_one_lt_d9, abs_nonneg (2*t)]
  have hH := marked_major_arc_log_height hb hL0.le hL5 ht
  have hW := marked_major_arc_weight hb hL0 hlog hq hH
  exact hbudget _ _ (mrt_VKLog_pos _) hH
    (zero_lt_one.trans_le (mrt_VKWeight_ge_one hH1)) hW

end ArtinMatthews
