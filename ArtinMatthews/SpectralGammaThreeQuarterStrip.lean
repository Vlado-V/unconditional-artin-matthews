module

public import ArtinMatthews.SpectralABLCoshCancellation
public import ArtinMatthews.SpectralGammaBetaComparison
public import ArtinMatthews.SpectralGammaHalfDecay
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set Complex
noncomputable section

theorem spectralGamma_three_quarter_compare :
    ∃ C : ℝ, 0 < C ∧ ∀ a t : ℝ, 3 / 4 ≤ a → a ≤ 9 / 4 →
      ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * I)‖ ≤
        C * ‖Complex.Gamma ((5 / 2 : ℂ) + (t : ℂ) * I)‖ := by
  have hcont : ContinuousOn Real.Gamma (Icc (3 / 4 : ℝ) (9 / 4)) := by
    intro a ha
    exact (Real.differentiableAt_Gamma (fun n => by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith [ha.1])).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (3 / 2) ⟨by norm_num, by norm_num⟩)
  have hGc : 0 < Real.Gamma (5 / 2) := Real.Gamma_pos_of_pos (by norm_num)
  refine ⟨(M + 1) / Real.Gamma (5 / 2), by positivity, ?_⟩
  intro a t ha0 ha1
  have ha : 0 < a := by linarith
  have hb : 0 < 5 / 2 - a := by linarith
  have hratio := spectralGamma_vertical_ratio_le a (5 / 2 - a) t ha hb
  rw [show a + (5 / 2 - a) = (5 / 2 : ℝ) by ring, norm_div] at hratio
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat] at hratio
  have hGa0 : |Real.Gamma a| ≤ M := by
    simpa only [Real.norm_eq_abs] using hM a ⟨ha0, ha1⟩
  have hGa : Real.Gamma a ≤ M + 1 := (le_abs_self _).trans (hGa0.trans (by linarith))
  have hnorm : 0 < ‖Complex.Gamma ((5 / 2 : ℂ) + (t : ℂ) * I)‖ := by
    apply norm_pos_iff.mpr
    exact Complex.Gamma_ne_zero_of_re_pos (by norm_num [Complex.mul_re])
  exact (div_le_iff₀ hnorm).mp (hratio.trans (div_le_div_of_nonneg_right hGa hGc.le))

theorem spectralABLCoshCancellation_exp_strip_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t y : ℝ, |y| ≤ 3 / 4 →
      Real.exp (Real.pi * |t|) * ‖spectralABLCoshCancellation ((t : ℂ) + (y : ℂ) * I)‖ ≤
        C * (1 + t ^ 2) ^ 2 := by
  obtain ⟨C, hC, hcomp⟩ := spectralGamma_three_quarter_compare
  refine ⟨(9 / 2) * C ^ 2, by positivity, ?_⟩
  intro t y hy
  let z : ℂ := (t : ℂ) + (y : ℂ) * I
  have hp : (3 / 2 : ℂ) + I * z = ((3 / 2 - y : ℝ) : ℂ) + (t : ℂ) * I := by
    dsimp [z]
    push_cast
    linear_combination (y : ℂ) * I_sq
  have hm : (3 / 2 : ℂ) - I * z = ((3 / 2 + y : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by
    dsimp [z]
    push_cast
    linear_combination -(y : ℂ) * I_sq
  have hpbound := hcomp (3 / 2 - y) t (by linarith [(abs_le.mp hy).2]) (by linarith [(abs_le.mp hy).1])
  have hmbound := hcomp (3 / 2 + y) (-t) (by linarith [(abs_le.mp hy).1]) (by linarith [(abs_le.mp hy).2])
  have heven : ‖Complex.Gamma ((5 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I)‖ =
      ‖Complex.Gamma ((5 / 2 : ℂ) + (t : ℂ) * I)‖ := by
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using spectralGamma_vertical_norm_even (5 / 2) t
  rw [heven] at hmbound
  have hprod : ‖Complex.Gamma ((3 / 2 : ℂ) + I * z)‖ *
      ‖Complex.Gamma ((3 / 2 : ℂ) - I * z)‖ ≤
        C ^ 2 * ‖Complex.Gamma ((5 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    rw [hp, hm]
    exact (mul_le_mul hpbound hmbound (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hcosh : 0 < Real.cosh (Real.pi * t) := Real.cosh_pos _
  have hbound : ‖spectralABLCoshCancellation z‖ ≤
      C ^ 2 * ((t ^ 2 + 1 / 4) * (t ^ 2 + 9 / 4)) / Real.cosh (Real.pi * t) := by
    unfold spectralABLCoshCancellation
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    calc
      _ ≤ (C ^ 2 * ‖Complex.Gamma ((5 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2) / Real.pi :=
        div_le_div_of_nonneg_right hprod Real.pi_pos.le
      _ = _ := by
        rw [spectralGamma_five_half_norm_sq]
        field_simp [Real.pi_ne_zero, ne_of_gt hcosh]
  have hexp : Real.exp (Real.pi * |t|) ≤ 2 * Real.cosh (Real.pi * t) := by
    rw [← Real.cosh_abs (Real.pi * t), abs_mul, abs_of_pos Real.pi_pos, Real.cosh_eq]
    linarith [Real.exp_pos (-(Real.pi * |t|))]
  have hpoly : (t ^ 2 + 1 / 4) * (t ^ 2 + 9 / 4) ≤ (9 / 4) * (1 + t ^ 2) ^ 2 := by
    have hp1 : t ^ 2 + 1 / 4 ≤ 1 + t ^ 2 := by linarith
    have hp2 : t ^ 2 + 9 / 4 ≤ (9 / 4) * (1 + t ^ 2) := by nlinarith [sq_nonneg t]
    exact (mul_le_mul hp1 hp2 (by positivity) (by positivity)).trans_eq (by ring)
  calc
    _ ≤ (2 * Real.cosh (Real.pi * t)) * ‖spectralABLCoshCancellation z‖ :=
      mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
    _ = 2 * (‖spectralABLCoshCancellation z‖ * Real.cosh (Real.pi * t)) := by ring
    _ ≤ 2 * (C ^ 2 * ((t ^ 2 + 1 / 4) * (t ^ 2 + 9 / 4))) :=
      mul_le_mul_of_nonneg_left ((le_div_iff₀ hcosh).mp hbound) (by norm_num)
    _ ≤ 2 * (C ^ 2 * ((9 / 4) * (1 + t ^ 2) ^ 2)) := by gcongr
    _ = _ := by ring

end
end ArtinMatthews
