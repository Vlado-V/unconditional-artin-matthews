module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import ArtinMatthews.SpectralBesselPoisson
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! The genuine modified first-kind Bessel series and its Poisson
integral, obtained from the existing actual complex-order J function. -/

noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators

namespace ArtinMatthews

def spectralBesselI (ν : ℂ) (x : ℝ) : ℂ :=
  (x/2 : ℂ)^ν*Complex.regularizedHGFun 0 {ν+1} ((x/2 : ℂ)^2)

theorem spectral_imaginary_cpow_scale {x : ℝ} (hx : 0 < x) (ν : ℂ) :
    (Complex.I*(x : ℂ)/2)^ν = Complex.I^ν*(x/2 : ℂ)^ν := by
  have hc : 0 < x/2 := div_pos hx (by norm_num)
  have hcC : (x/2 : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hleft : Complex.I*(x : ℂ)/2 ≠ 0 := div_ne_zero
    (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')) (by norm_num)
  have hlog : Complex.log (Complex.I*(x : ℂ)/2) = Complex.log Complex.I+Complex.log (x/2 : ℂ) := by
    calc
      _ = Complex.log (((x/2 : ℝ) : ℂ)*Complex.I) := by congr 1; push_cast; ring
      _ = ((Real.log (x/2) : ℝ) : ℂ)+Complex.log Complex.I := Complex.log_ofReal_mul hc Complex.I_ne_zero
      _ = _ := by rw [Complex.ofReal_log hc.le,Complex.ofReal_div,Complex.ofReal_ofNat]; ring
  rw [Complex.cpow_def_of_ne_zero hleft,Complex.cpow_def_of_ne_zero Complex.I_ne_zero,
    Complex.cpow_def_of_ne_zero hcC,hlog,add_mul,Complex.exp_add]

theorem spectralBesselI_besselJ {x : ℝ} (hx : 0 < x) (ν : ℂ) :
    Complex.besselJ ν (Complex.I*x) = Complex.I^ν*spectralBesselI ν x := by
  rw [Complex.besselJ_def]
  dsimp only
  rw [spectral_imaginary_cpow_scale hx]
  have harg : -(Complex.I*(x : ℂ)/2)^2 = (x/2 : ℂ)^2 := by
    rw [div_pow,mul_pow,Complex.I_sq]
    ring
  rw [harg]
  unfold spectralBesselI
  ring

theorem spectralBesselI_poisson (ν : ℂ) {x : ℝ} (hx : 0 < x) (hν : -(1/2 : ℝ) < ν.re) :
    spectralBesselI ν x = (x/2 : ℂ)^ν/((Real.sqrt Real.pi : ℂ)*Complex.Gamma (ν+1/2))*
      ∫ u : ℝ in (-1 : ℝ)..1,
        Complex.exp ((-x*u : ℝ) : ℂ)*(1-(u : ℂ)^2)^(ν-1/2) := by
  have h := spectral_besselJ_poisson ν (Complex.I*x) hν
  rw [spectralBesselI_besselJ hx,spectral_imaginary_cpow_scale hx] at h
  have he (u : ℝ) : Complex.I*(Complex.I*(x : ℂ))*(u : ℂ) = ((-x*u : ℝ) : ℂ) := by
    rw [← mul_assoc,Complex.I_mul_I]
    push_cast
    ring
  simp_rw [he] at h
  have hInu : Complex.I^ν ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero Complex.I_ne_zero]
    exact Complex.exp_ne_zero _
  apply mul_left_cancel₀ hInu
  calc
    _ = (Complex.I^ν*(x/2 : ℂ)^ν)/((Real.sqrt Real.pi : ℂ)*Complex.Gamma (ν+1/2))*
        ∫ u : ℝ in (-1 : ℝ)..1,
          Complex.exp ((-x*u : ℝ) : ℂ)*(1-(u : ℂ)^2)^(ν-1/2) := h
    _ = _ := by ring

end ArtinMatthews
