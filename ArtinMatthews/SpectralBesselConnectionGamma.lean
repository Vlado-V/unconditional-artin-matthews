module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import ArtinMatthews.SpectralGammaReflectionStrip
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! The exact Gamma algebra behind the K/I connection.  The natural
common strip keeps every reflection argument between real parts zero and one. -/

noncomputable section

namespace ArtinMatthews

theorem spectralBesselConnection_gamma (ν s : ℂ)
    (hs : |ν.re| < s.re) (hsh : s.re < 1/2) :
    ((Real.pi : ℂ)/2)*
      ((2 : ℂ)^(-s)*Complex.Gamma (s-ν)*Complex.Gamma (1/2-s)/
          ((Real.sqrt Real.pi : ℂ)*Complex.Gamma (-ν+1-s))-
        (2 : ℂ)^(-s)*Complex.Gamma (s+ν)*Complex.Gamma (1/2-s)/
          ((Real.sqrt Real.pi : ℂ)*Complex.Gamma (ν+1-s))) =
      Complex.sin ((Real.pi : ℂ)*ν)*
        ((Real.sqrt Real.pi : ℂ)*(2 : ℂ)^(-s)*Complex.Gamma (s+ν)*
          Complex.Gamma (s-ν)/Complex.Gamma (s+1/2)) := by
  have ha0 : 0 < (s+ν).re := by simp only [Complex.add_re]; linarith [neg_le_abs ν.re]
  have hb0 : 0 < (s-ν).re := by simp only [Complex.sub_re]; linarith [le_abs_self ν.re]
  have ha1 : (s+ν).re < 1 := by simp only [Complex.add_re]; linarith [le_abs_self ν.re]
  have hb1 : (s-ν).re < 1 := by simp only [Complex.sub_re]; linarith [neg_le_abs ν.re]
  have hsa : -(1/2 : ℝ) < s.re := by linarith [abs_nonneg ν.re]
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hq : (Real.sqrt Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hq2 : (Real.sqrt Real.pi : ℂ)^2 = (Real.pi : ℂ) := by
    exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  have hA := spectral_Gamma_inv_reflection (s+ν) ha0 ha1
  have hB := spectral_Gamma_inv_reflection (s-ν) hb0 hb1
  have hC := spectral_Gamma_half_cos_reflection s hsa hsh
  have hr : (Real.pi : ℂ)/(Real.sqrt Real.pi : ℂ) = (Real.sqrt Real.pi : ℂ) := by
    apply (div_eq_iff hq).mpr
    simpa only [pow_two] using hq2.symm
  rw [show (-ν : ℂ)+1-s = 1-(s+ν) by ring,
    show (ν : ℂ)+1-s = 1-(s-ν) by ring]
  simp only [div_eq_mul_inv,mul_inv]
  rw [hA,hB]
  calc
    _ = ((2 : ℂ)^(-s)*Complex.Gamma (s+ν)*Complex.Gamma (s-ν)*
        Complex.Gamma (1/2-s)/(2*(Real.sqrt Real.pi : ℂ)))*
        (Complex.sin ((Real.pi : ℂ)*(s+ν))-Complex.sin ((Real.pi : ℂ)*(s-ν))) := by
      field_simp [hp]
    _ = ((2 : ℂ)^(-s)*Complex.Gamma (s+ν)*Complex.Gamma (s-ν)/(Real.sqrt Real.pi : ℂ))*
        (Complex.Gamma (1/2-s)*Complex.cos ((Real.pi : ℂ)*s))*
        Complex.sin ((Real.pi : ℂ)*ν) := by
      rw [spectral_sin_sum_sub_difference]
      ring_nf
    _ = Complex.sin ((Real.pi : ℂ)*ν)*
        (((Real.pi : ℂ)/(Real.sqrt Real.pi : ℂ))*(2 : ℂ)^(-s)*
          Complex.Gamma (s+ν)*Complex.Gamma (s-ν)/Complex.Gamma (s+1/2)) := by
      rw [hC]
      ring_nf
    _ = _ := by rw [hr]; ring_nf

end ArtinMatthews
