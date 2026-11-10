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


set_option backward.privateInPublic true
@[expose] public section

/-! Arbitrarily many logarithmic Fourier moments absorb the two powers
of logarithm from the actual dyadic partition. -/

namespace ArtinMatthews

open Filter
open scoped Asymptotics Topology

theorem prime_extraction_log_moment_decay (A : ℝ) {k : ℕ}
    (hk : A + 2 < (k : ℝ)) :
    (fun x : ℝ => x * (Real.log x) ^ 2 / (Real.log x) ^ k) =o[atTop]
      (fun x : ℝ => x * (Real.log x) ^ (-A)) := by
  apply Asymptotics.isLittleO_of_tendsto'
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact fun h => (mul_pos (by linarith : 0 < x)
      (Real.rpow_pos_of_pos (Real.log_pos hx) (-A))).ne' h |>.elim
  · have hlim := (tendsto_rpow_neg_atTop (by linarith : 0 < (k : ℝ) - 2 - A)).comp
      Real.tendsto_log_atTop
    apply hlim.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hl : 0 < Real.log x := Real.log_pos hx
    change (Real.log x) ^ (-((k : ℝ) - 2 - A)) = _
    rw [show -((k : ℝ) - 2 - A) = (2 : ℝ) + A - k by ring,
      Real.rpow_sub hl, Real.rpow_add hl, Real.rpow_neg hl.le]
    rw [Real.rpow_natCast, Real.rpow_two]
    field_simp

theorem prime_extraction_all_log_moments_isLittleO (F : ℝ → ℂ)
    (hF : ∀ k : ℕ, ∃ C : ℝ, ∀ᶠ x : ℝ in atTop,
      ‖F x‖ ≤ C * x * (Real.log x) ^ 2 / (Real.log x) ^ k) (A : ℝ) :
    F =o[atTop] (fun x : ℝ => x * (Real.log x) ^ (-A)) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (A + 2)
  obtain ⟨C, hC⟩ := hF k
  have hb : F =O[atTop] (fun x : ℝ => x * (Real.log x) ^ 2 / (Real.log x) ^ k) := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [hC, eventually_gt_atTop (1 : ℝ)] with x hbound hx
    have hp : 0 < x * (Real.log x) ^ 2 / (Real.log x) ^ k :=
      div_pos (mul_pos (by linarith) (pow_pos (Real.log_pos hx) _))
        (pow_pos (Real.log_pos hx) _)
    rw [Real.norm_eq_abs, abs_of_pos hp]
    convert hbound using 1
    ring
  exact hb.trans_isLittleO (prime_extraction_log_moment_decay A hk)

end ArtinMatthews
