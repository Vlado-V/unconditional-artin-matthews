module

public import ArtinMatthews.SpectralBesselI
public import ArtinMatthews.SpectralBesselSeriesOrderBound
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! The actual I series satisfies the same vertical-order majorant as J. -/

noncomputable section
open scoped BigOperators

namespace ArtinMatthews

theorem spectralBesselI_eq_hypergeometric_tsum (ν : ℂ) (x : ℝ) :
    spectralBesselI ν x = (x/2 : ℂ)^ν*
      ∑' n : ℕ, ((x/2 : ℂ)^2)^n/((n.factorial : ℂ)*Complex.Gamma (ν+1+n)) := by
  unfold spectralBesselI Complex.regularizedHGFun Complex.regularizedHGFunSeries
  rw [← FormalMultilinearSeries.ofScalarsSum,FormalMultilinearSeries.ofScalars_sum_eq]
  congr 1
  apply tsum_congr
  intro n
  simp [Complex.regularizedHGFunCoeff,smul_eq_mul,div_eq_mul_inv,mul_comm]

theorem spectralBesselI_norm_le_exp_of_re_zero (ν : ℂ) (hν : ν.re = 0)
    {x : ℝ} (hx : 0 < x) :
    ‖spectralBesselI ν x‖ ≤ Real.exp (x^2/4)/‖Complex.Gamma (ν+1)‖ := by
  have hnormpref : ‖(x/2 : ℂ)^ν‖ = 1 := by
    rw [show (x/2 : ℂ) = ((x/2 : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (half_pos hx),hν,Real.rpow_zero]
  rw [spectralBesselI_eq_hypergeometric_tsum,norm_mul,hnormpref,one_mul]
  have h := spectral_gamma_series_norm_le_exp (ν+1) ((x/2 : ℂ)^2) (by simpa using hν)
  have hn : ‖(x/2 : ℂ)^2‖ = x^2/4 := by
    rw [norm_pow]
    have he : (x/2 : ℂ) = ((x/2 : ℝ) : ℂ) := by push_cast; rfl
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (half_pos hx)]
    ring
  simpa only [hn] using h

end ArtinMatthews
