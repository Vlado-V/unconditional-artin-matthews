module

public import ArtinMatthews.SpectralBesselI
public import ArtinMatthews.SpectralBesselIOrderBound
public import ArtinMatthews.SpectralBesselPoissonSeries
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

noncomputable section
open scoped BigOperators

namespace ArtinMatthews

theorem spectral_Gamma_shift_norm_lower_of_one_le (w : ℂ) (hw : 1 ≤ w.re) (n : ℕ) :
    (n.factorial : ℝ) * ‖Complex.Gamma w‖ ≤ ‖Complex.Gamma (w+n)‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hre : 0 < (w+(n : ℂ)).re := by
      simp only [Complex.add_re, Complex.natCast_re]
      positivity
    have hne : w+(n : ℂ) ≠ 0 := by
      intro h
      rw [h, Complex.zero_re] at hre
      exact lt_irrefl _ hre
    have hfactor : (n+1 : ℝ) ≤ ‖w+(n : ℂ)‖ := by
      calc
        _ ≤ (w+(n : ℂ)).re := by
          simp only [Complex.add_re, Complex.natCast_re]
          linarith
        _ ≤ _ := Complex.re_le_norm _
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_add, Nat.cast_one, ← add_assoc, Complex.Gamma_add_one _ hne, norm_mul]
    calc
      _ = ((n : ℝ)+1)*((n.factorial : ℝ)*‖Complex.Gamma w‖) := by ring
      _ ≤ ‖w+(n : ℂ)‖*‖Complex.Gamma (w+(n : ℂ))‖ :=
        mul_le_mul hfactor ih (by positivity) (norm_nonneg _)

theorem spectral_Gamma_shift_norm_lower_base_of_one_le (w : ℂ) (hw : 1 ≤ w.re)
    (n : ℕ) : ‖Complex.Gamma w‖ ≤ ‖Complex.Gamma (w+n)‖ := by
  calc
    _ = 1*‖Complex.Gamma w‖ := by ring
    _ ≤ (n.factorial : ℝ)*‖Complex.Gamma w‖ := by
      gcongr
      exact_mod_cast Nat.factorial_pos n
    _ ≤ _ := spectral_Gamma_shift_norm_lower_of_one_le w hw n

theorem spectral_gamma_series_norm_le_exp_of_one_le (w z : ℂ) (hw : 1 ≤ w.re) :
    ‖∑' n : ℕ, z^n/((n.factorial : ℂ)*Complex.Gamma (w+n))‖ ≤
      Real.exp ‖z‖/‖Complex.Gamma w‖ := by
  have hG : 0 < ‖Complex.Gamma w‖ := norm_pos_iff.mpr
    (Complex.Gamma_ne_zero_of_re_pos (by linarith))
  have hs : Summable (fun n : ℕ => z^n/((n.factorial : ℂ)*Complex.Gamma (w+n))) := by
    have h := (Complex.regularizedHGFunSeries 0 {w}).summable (x := z) (by simp)
    simpa [Complex.regularizedHGFunSeries, FormalMultilinearSeries.ofScalars_apply_eq,
      Complex.regularizedHGFunCoeff, smul_eq_mul, div_eq_mul_inv, mul_comm] using h
  have hbound (n : ℕ) : ‖z^n/((n.factorial : ℂ)*Complex.Gamma (w+n))‖ ≤
      (‖z‖^n/(n.factorial : ℝ))/‖Complex.Gamma w‖ := by
    rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast, div_div]
    apply div_le_div_of_nonneg_left (by positivity)
      (mul_pos (by exact_mod_cast Nat.factorial_pos n) hG)
    exact mul_le_mul_of_nonneg_left
      (spectral_Gamma_shift_norm_lower_base_of_one_le w hw n) (by positivity)
  have hsum := (NormedSpace.expSeries_div_summable ‖z‖).div_const ‖Complex.Gamma w‖
  calc
    _ ≤ ∑' n : ℕ, ‖z^n/((n.factorial : ℂ)*Complex.Gamma (w+n))‖ :=
      norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' n : ℕ, (‖z‖^n/(n.factorial : ℝ))/‖Complex.Gamma w‖ :=
      hs.norm.tsum_le_tsum hbound hsum
    _ = _ := by
      rw [tsum_div_const]
      congr 1
      simpa only [Real.exp_eq_exp_ℝ] using (NormedSpace.expSeries_div_hasSum_exp ‖z‖).tsum_eq

theorem spectral_besselJ_norm_le_exp_of_re_nonneg (ν : ℂ) (hν : 0 ≤ ν.re)
    {x : ℝ} (hx : 0 < x) :
    ‖Complex.besselJ ν (x : ℂ)‖ ≤
      (x/2) ^ ν.re * Real.exp (x^2/4) / ‖Complex.Gamma (ν+1)‖ := by
  have hnormpref : ‖(x/2 : ℂ)^ν‖ = (x/2) ^ ν.re := by
    rw [show (x/2 : ℂ) = ((x/2 : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (half_pos hx)]
  rw [besselJ_eq_hypergeometric_tsum, norm_mul, hnormpref]
  have h := spectral_gamma_series_norm_le_exp_of_one_le (ν+1) (-(x/2 : ℂ)^2)
    (by simpa using hν)
  have hn : ‖-(x/2 : ℂ)^2‖ = x^2/4 := by
    rw [norm_neg, norm_pow]
    have he : (x/2 : ℂ) = ((x/2 : ℝ) : ℂ) := by push_cast; rfl
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hx)]
    ring
  simpa only [hn, mul_div_assoc] using
    mul_le_mul_of_nonneg_left h (Real.rpow_nonneg (by positivity) _)

theorem spectralBesselI_norm_le_exp_of_re_nonneg (ν : ℂ) (hν : 0 ≤ ν.re)
    {x : ℝ} (hx : 0 < x) :
    ‖spectralBesselI ν x‖ ≤
      (x/2) ^ ν.re * Real.exp (x^2/4) / ‖Complex.Gamma (ν+1)‖ := by
  have hnormpref : ‖(x/2 : ℂ)^ν‖ = (x/2) ^ ν.re := by
    rw [show (x/2 : ℂ) = ((x/2 : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (half_pos hx)]
  rw [spectralBesselI_eq_hypergeometric_tsum, norm_mul, hnormpref]
  have h := spectral_gamma_series_norm_le_exp_of_one_le (ν+1) ((x/2 : ℂ)^2)
    (by simpa using hν)
  have hn : ‖(x/2 : ℂ)^2‖ = x^2/4 := by
    rw [norm_pow]
    have he : (x/2 : ℂ) = ((x/2 : ℝ) : ℂ) := by push_cast; rfl
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hx)]
    ring
  simpa only [hn, mul_div_assoc] using
    mul_le_mul_of_nonneg_left h (Real.rpow_nonneg (by positivity) _)

end ArtinMatthews
