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

/-! Pure numerical absorption for the dirty major-arc branch.  This file does
not assume or supply a row-count estimate: it absorbs its exponential envelope
uniformly over all permitted memory sizes and lengths. -/

namespace ArtinMatthews
open Filter
open scoped Topology

theorem marked_polynomial_exp_eventually_le (C A P : ℝ) {δ b ε : ℝ}
    (hδ : 0 < δ) (hb : 0 < b) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, C * L ^ A * Real.exp (-b * L ^ δ) ≤ ε * L ^ (-P) := by
  have ht := (rpow_mul_exp_neg_rpow_tendsto (A + P) hδ hb).const_mul C
  simp only [mul_zero] at ht
  filter_upwards [ht.eventually (Iio_mem_nhds hε), eventually_gt_atTop (0 : ℝ)]
    with L hsmall hL
  have hp : L ^ (A + P) * L ^ (-P) = L ^ A := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  calc
    _ = (C * (L ^ (A + P) * Real.exp (-b * L ^ δ))) * L ^ (-P) := by
      calc
        _ = C * (L ^ (A + P) * L ^ (-P)) * Real.exp (-b * L ^ δ) := by rw [hp]
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall.le (Real.rpow_nonneg hL.le _)

theorem marked_length_negative_rpow_le {L Y c δ τ : ℝ}
    (hτ : 0 ≤ τ) (hY : Real.exp (c * L ^ δ) ≤ Y) :
    Y ^ (-τ) ≤ Real.exp (-(c * τ) * L ^ δ) := by
  calc
    _ ≤ (Real.exp (c * L ^ δ)) ^ (-τ) :=
      Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hY (by linarith)
    _ = _ := by rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]; congr 1; ring

theorem marked_dirty_major_budget_general {C C_B : ℝ} (hC : 0 ≤ C)
    (hC_B : 0 ≤ C_B) (A b P : ℝ) (K : ℕ) {c δ τ : ℝ}
    (hc : 0 < c) (hδ : 0 < δ) (hτ : 0 < τ) :
    ∀ᶠ L : ℝ in atTop, ∀ B Y : ℝ, 0 ≤ B → B ≤ C_B * L ^ b →
      Real.exp (c * L ^ δ) ≤ Y →
      C * L ^ A * B ^ K * (Real.exp (-L ^ δ) + Y ^ (-τ)) ≤ L ^ (-P) := by
  filter_upwards [marked_polynomial_exp_eventually_le (C * C_B ^ K)
      (A + b * (K : ℝ)) P hδ (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1 / 2),
    marked_polynomial_exp_eventually_le (C * C_B ^ K)
      (A + b * (K : ℝ)) P hδ (mul_pos hc hτ)
      (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_gt_atTop (0 : ℝ)] with L hfirst hsecond hL
  intro B Y hB hBupper hY
  have hpow : B ^ K ≤ C_B ^ K * L ^ (b * (K : ℝ)) := by
    calc
      _ ≤ (C_B * L ^ b) ^ K := pow_le_pow_left₀ hB hBupper K
      _ = _ := by rw [mul_pow, ← Real.rpow_mul_natCast hL.le]
  have hfactor : C * L ^ A * B ^ K ≤ (C * C_B ^ K) * L ^ (A + b * (K : ℝ)) := by
    calc
      _ ≤ C * L ^ A * (C_B ^ K * L ^ (b * (K : ℝ))) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by rw [Real.rpow_add hL]; ring
  have hlen := marked_length_negative_rpow_le hτ.le hY
  have henv : 0 ≤ Real.exp (-L ^ δ) + Y ^ (-τ) := by
    have hYpos : 0 < Y := (Real.exp_pos _).trans_le hY
    positivity
  calc
    _ ≤ ((C * C_B ^ K) * L ^ (A + b * (K : ℝ))) *
        (Real.exp (-L ^ δ) + Y ^ (-τ)) := mul_le_mul_of_nonneg_right hfactor henv
    _ ≤ ((C * C_B ^ K) * L ^ (A + b * (K : ℝ))) *
        (Real.exp (-L ^ δ) + Real.exp (-(c * τ) * L ^ δ)) := by gcongr
    _ = (C * C_B ^ K) * L ^ (A + b * (K : ℝ)) * Real.exp (-L ^ δ) +
        (C * C_B ^ K) * L ^ (A + b * (K : ℝ)) * Real.exp (-(c * τ) * L ^ δ) := by ring
    _ ≤ (1 / 2) * L ^ (-P) + (1 / 2) * L ^ (-P) := by
      simpa only [neg_mul, one_mul] using add_le_add hfirst hsecond
    _ = _ := by ring

theorem marked_dirty_major_budget {C C_B : ℝ} (hC : 0 ≤ C) (hC_B : 0 ≤ C_B)
    (A₀ b P : ℝ) (K : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ B Y : ℝ, 0 ≤ B → B ≤ C_B * L ^ b →
      Real.exp (c * L ^ (1 / 10 : ℝ)) ≤ Y →
      C * L ^ (3 * A₀) * B ^ K *
        (Real.exp (-L ^ (1 / 10 : ℝ)) + Y ^ (-(1 / 10 : ℝ))) ≤ L ^ (-P) :=
  marked_dirty_major_budget_general hC hC_B (3 * A₀) b P K hc (by norm_num) (by norm_num)

theorem marked_dirty_major_cutoff_budget {C C_B : ℝ} (hC : 0 ≤ C) (hC_B : 0 ≤ C_B)
    (A₀ b P : ℝ) (K : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ Q B Y : ℝ, 0 ≤ Q → Q ≤ L ^ A₀ →
      0 ≤ B → B ≤ C_B * L ^ b → Real.exp (c * L ^ (1 / 10 : ℝ)) ≤ Y →
      C * Q ^ 3 * B ^ K *
        (Real.exp (-L ^ (1 / 10 : ℝ)) + Y ^ (-(1 / 10 : ℝ))) ≤ L ^ (-P) := by
  filter_upwards [marked_dirty_major_budget hC hC_B A₀ b P K hc,
    eventually_gt_atTop (0 : ℝ)] with L hbudget hL
  intro Q B Y hQ hQupper hB hBupper hY
  have hcube : Q ^ 3 ≤ L ^ (3 * A₀) := by
    calc
      _ ≤ (L ^ A₀) ^ 3 := pow_le_pow_left₀ hQ hQupper 3
      _ = _ := by rw [← Real.rpow_mul_natCast hL.le]; congr 1; norm_num; ring
  have hYpos : 0 < Y := (Real.exp_pos _).trans_le hY
  calc
    _ ≤ C * L ^ (3 * A₀) * B ^ K *
        (Real.exp (-L ^ (1 / 10 : ℝ)) + Y ^ (-(1 / 10 : ℝ))) := by gcongr
    _ ≤ _ := hbudget B Y hB hBupper hY

end ArtinMatthews
