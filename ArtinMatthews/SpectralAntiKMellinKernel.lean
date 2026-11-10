module

public import ArtinMatthews.SpectralAntiCoshBeta
public import Mathlib.Analysis.CStarAlgebra.Classes
public import ArtinMatthews.SpectralLaplaceGamma
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Data.Nat.Choose.Multinomial
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
import OAI.NumberTheory.DirichletL.Eisenstein.Rows


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute Laplace/Mellin Fubini for exp(x) times the actual K kernel.
The natural strip |Re nu|<Re s<1/2 is proved through the cosh-minus-one beta profile. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein

namespace ArtinMatthews

private theorem cosh_sub_one_pos {u : ℝ} (hu : 0 < u) : 0 < Real.cosh u-1 := by
  rw [spectral_cosh_sub_one_exp hu]
  have hv : 0 < 1-Real.exp (-u) := by
    have h : Real.exp (-u) < 1 := by simpa using Real.exp_lt_exp.mpr (neg_lt_zero.mpr hu)
    linarith
  exact div_pos (mul_pos hv hv) (mul_pos two_pos (Real.exp_pos _))

def spectralAntiKMellinKernel (ν s : ℂ) (u x : ℝ) : ℂ :=
  Complex.exp (ν*(u : ℂ))*((x : ℂ)^(s-1)*
    Complex.exp (-((Real.cosh u-1 : ℝ) : ℂ)*(x : ℂ)))

theorem spectralAntiKMellinKernel_slice_integrable (ν s : ℂ) (hs : 0 < s.re) {u : ℝ} (hu : 0 < u) :
    IntegrableOn (spectralAntiKMellinKernel ν s u) (Ioi (0 : ℝ)) :=
  (spectralLaplaceGamma_integrable s hs (cosh_sub_one_pos hu)).const_mul _

theorem spectralAntiKMellinKernel_integral_x (ν s : ℂ) (hs : 0 < s.re) {u : ℝ} (hu : 0 < u) :
    (∫ x in Ioi (0 : ℝ), spectralAntiKMellinKernel ν s u x) =
      Complex.Gamma s*spectralAntiCoshBetaProfile s ν u := by
  have hc : 0 < Real.cosh u-1 := cosh_sub_one_pos hu
  unfold spectralAntiKMellinKernel spectralAntiCoshBetaProfile
  rw [integral_const_mul,spectralLaplaceGamma_integral s hs hc,one_div,
    Complex.inv_cpow_ofReal_nonneg hc.le,← Complex.cpow_neg]
  ring_nf

theorem spectralAntiKMellinKernel_norm (ν s : ℂ) (u : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖spectralAntiKMellinKernel ν s u x‖ =
      Real.exp (ν.re*u)*(x^(s.re-1)*Real.exp (-(Real.cosh u-1)*x)) := by
  unfold spectralAntiKMellinKernel
  rw [norm_mul,norm_mul,Complex.norm_exp,Complex.norm_exp,Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,
    Complex.sub_re,Complex.one_re,Complex.neg_re]

theorem spectralAntiKMellinKernel_integral_norm (ν s : ℂ) (hs : 0 < s.re) {u : ℝ} (hu : 0 < u) :
    (∫ x in Ioi (0 : ℝ), ‖spectralAntiKMellinKernel ν s u x‖) =
      Real.Gamma s.re*‖spectralAntiCoshBetaProfile s ν u‖ := by
  have hc : 0 < Real.cosh u-1 := cosh_sub_one_pos hu
  calc
    _ = ∫ x in Ioi (0 : ℝ), Real.exp (ν.re*u)*(x^(s.re-1)*Real.exp (-(Real.cosh u-1)*x)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact spectralAntiKMellinKernel_norm ν s u hx
    _ = Real.exp (ν.re*u)*((1/(Real.cosh u-1))^s.re*Real.Gamma s.re) := by
      rw [integral_const_mul]
      congr 1
      simpa only [neg_mul] using Real.integral_rpow_mul_exp_neg_mul_Ioi hs hc
    _ = _ := by
      unfold spectralAntiCoshBetaProfile
      rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hc,Complex.norm_exp]
      simp only [Complex.neg_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
      rw [one_div,← Real.rpow_neg_eq_inv_rpow]
      ring_nf

theorem spectralAntiKMellinKernel_integrable (ν s : ℂ)
    (hs : |ν.re| < s.re) (hsh : s.re < 1/2) :
    Integrable (fun p : ℝ × ℝ => spectralAntiKMellinKernel ν s p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hs0 : 0 < s.re := (abs_nonneg ν.re).trans_lt hs
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => spectralAntiKMellinKernel ν s p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    unfold spectralAntiKMellinKernel
    fun_prop
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact spectralAntiKMellinKernel_slice_integrable ν s hs0 hu
  · apply ((spectralAntiCoshBetaProfile_integrable s ν ((le_abs_self ν.re).trans_lt hs)
      hsh).norm.const_mul (Real.Gamma s.re)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (spectralAntiKMellinKernel_integral_norm ν s hs0 hu).symm

end ArtinMatthews
