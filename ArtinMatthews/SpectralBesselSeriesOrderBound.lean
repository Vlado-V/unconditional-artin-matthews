module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import ArtinMatthews.SpectralBesselPoissonSeries
public import ArtinMatthews.SpectralGammaShiftNorm
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

/-! Uniform imaginary-order series bounds with the exact Gamma factor.
The spatial majorant exp(x^2/4) permits Gaussian Fubini for p>1/4. -/

noncomputable section
open scoped BigOperators

namespace ArtinMatthews

theorem spectral_gamma_series_norm_le_exp (w z : ℂ) (hw : w.re = 1) :
    ‖∑' n : ℕ, z^n/((n.factorial : ℂ)*Complex.Gamma (w+n))‖ ≤
      Real.exp ‖z‖/‖Complex.Gamma w‖ := by
  have hG : 0 < ‖Complex.Gamma w‖ := norm_pos_iff.mpr
    (Complex.Gamma_ne_zero_of_re_pos (by rw [hw]; norm_num))
  have hs : Summable (fun n : ℕ => z^n/((n.factorial : ℂ)*Complex.Gamma (w+n))) := by
    have h := (Complex.regularizedHGFunSeries 0 {w}).summable (x := z) (by simp)
    simpa [Complex.regularizedHGFunSeries,FormalMultilinearSeries.ofScalars_apply_eq,
      Complex.regularizedHGFunCoeff,smul_eq_mul,div_eq_mul_inv,mul_comm] using h
  have hbound (n : ℕ) : ‖z^n/((n.factorial : ℂ)*Complex.Gamma (w+n))‖ ≤
      (‖z‖^n/(n.factorial : ℝ))/‖Complex.Gamma w‖ := by
    rw [norm_div,norm_mul,norm_pow,Complex.norm_natCast,div_div]
    apply div_le_div_of_nonneg_left (by positivity)
      (mul_pos (by exact_mod_cast Nat.factorial_pos n) hG)
    exact mul_le_mul_of_nonneg_left (spectral_Gamma_shift_norm_lower_base w hw n) (by positivity)
  have hsum := (NormedSpace.expSeries_div_summable ‖z‖).div_const ‖Complex.Gamma w‖
  calc
    _ ≤ ∑' n : ℕ, ‖z^n/((n.factorial : ℂ)*Complex.Gamma (w+n))‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' n : ℕ, (‖z‖^n/(n.factorial : ℝ))/‖Complex.Gamma w‖ :=
      hs.norm.tsum_le_tsum hbound hsum
    _ = _ := by
      rw [tsum_div_const]
      congr 1
      simpa only [Real.exp_eq_exp_ℝ] using (NormedSpace.expSeries_div_hasSum_exp ‖z‖).tsum_eq

theorem spectral_besselJ_norm_le_exp_of_re_zero (ν : ℂ) (hν : ν.re = 0)
    {x : ℝ} (hx : 0 < x) :
    ‖Complex.besselJ ν (x : ℂ)‖ ≤ Real.exp (x^2/4)/‖Complex.Gamma (ν+1)‖ := by
  have hnormpref : ‖(x/2 : ℂ)^ν‖ = 1 := by
    rw [show (x/2 : ℂ) = ((x/2 : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (half_pos hx),hν,Real.rpow_zero]
  rw [besselJ_eq_hypergeometric_tsum,norm_mul,hnormpref,one_mul]
  have h := spectral_gamma_series_norm_le_exp (ν+1) (-(x/2 : ℂ)^2) (by simpa using hν)
  have hn : ‖-(x/2 : ℂ)^2‖ = x^2/4 := by
    rw [norm_neg,norm_pow]
    have he : (x/2 : ℂ) = ((x/2 : ℝ) : ℂ) := by push_cast; rfl
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (half_pos hx)]
    ring
  simpa only [hn] using h

end ArtinMatthews
