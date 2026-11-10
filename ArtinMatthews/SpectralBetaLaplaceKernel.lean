module

public import ArtinMatthews.SpectralUnitBeta
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute beta/Laplace interchange.  The restrictions Re(s)>0,
Re(a-s)>0, Re(b)>0 account for all three improper boundaries. -/

noncomputable section
open Set MeasureTheory Filter

namespace ArtinMatthews

def spectralBetaLaplaceKernel (a b s : ℂ) (t x : ℝ) : ℂ :=
  spectralUnitBetaProfile a b t*((x : ℂ)^(s-1)*Complex.exp (-((2*t : ℝ) : ℂ)*(x : ℂ)))

theorem spectralBetaLaplaceKernel_slice_integrable (a b s : ℂ)
    (hs : 0 < s.re) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (spectralBetaLaplaceKernel a b s t) (Ioi (0 : ℝ)) :=
  (spectralLaplaceGamma_integrable s hs (mul_pos two_pos ht)).const_mul _

theorem spectralBetaLaplaceKernel_integral_x (a b s : ℂ)
    (hs : 0 < s.re) {t : ℝ} (ht : 0 < t) :
    (∫ x in Ioi (0 : ℝ), spectralBetaLaplaceKernel a b s t x) =
      ((2 : ℂ)^(-s)*Complex.Gamma s)*spectralUnitBetaProfile (a-s) b t := by
  unfold spectralBetaLaplaceKernel
  rw [integral_const_mul,spectralLaplaceGamma_integral s hs (mul_pos two_pos ht)]
  have hp : (1/((2*t : ℝ) : ℂ))^s = (2 : ℂ)^(-s)*(t : ℂ)^(-s) := by
    rw [one_div,Complex.inv_cpow_ofReal_nonneg (mul_nonneg zero_le_two ht.le),
      ← Complex.cpow_neg]
    simpa only [Complex.ofReal_mul,Complex.ofReal_ofNat] using
      Complex.mul_cpow_ofReal_nonneg zero_le_two ht.le (-s)
  rw [hp]
  unfold spectralUnitBetaProfile
  have he : (t : ℂ)^(a-1)*(t : ℂ)^(-s) = (t : ℂ)^(a-s-1) := by
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht.ne')]
    congr 1
    ring
  calc
    _ = ((2 : ℂ)^(-s)*Complex.Gamma s)*
        ((t : ℂ)^(a-1)*(t : ℂ)^(-s))*(1-(t : ℂ))^(b-1) := by ring
    _ = _ := by rw [he]; ring

theorem spectralBetaLaplaceKernel_norm (a b s : ℂ) {t x : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) :
    ‖spectralBetaLaplaceKernel a b s t x‖ =
      (t^(a.re-1)*(1-t)^(b.re-1))*(x^(s.re-1)*Real.exp (-(2*t)*x)) := by
  unfold spectralBetaLaplaceKernel
  rw [norm_mul,spectralUnitBetaProfile_norm a b ht,norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx,Complex.norm_exp]
  simp only [Complex.sub_re,Complex.one_re,Complex.mul_re,Complex.neg_re,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]

theorem spectralBetaLaplaceKernel_integral_norm (a b s : ℂ)
    (hs : 0 < s.re) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (∫ x in Ioi (0 : ℝ), ‖spectralBetaLaplaceKernel a b s t x‖) =
      (2^(-s.re)*Real.Gamma s.re)*‖spectralUnitBetaProfile (a-s) b t‖ := by
  calc
    _ = (t^(a.re-1)*(1-t)^(b.re-1))*
        ((1/(2*t))^s.re*Real.Gamma s.re) := by
      calc
        _ = ∫ x in Ioi (0 : ℝ),
            (t^(a.re-1)*(1-t)^(b.re-1))*(x^(s.re-1)*Real.exp (-(2*t)*x)) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x hx
          exact spectralBetaLaplaceKernel_norm a b s ht hx
        _ = _ := by
          rw [integral_const_mul]
          congr 1
          simpa only [neg_mul] using
            Real.integral_rpow_mul_exp_neg_mul_Ioi hs (mul_pos two_pos ht.1)
    _ = _ := by
      rw [spectralUnitBetaProfile_norm (a-s) b ht,one_div,
        ← Real.rpow_neg_eq_inv_rpow,Real.mul_rpow zero_le_two ht.1.le]
      have he : t^(a.re-1)*t^(-s.re) = t^((a-s).re-1) := by
        rw [← Real.rpow_add ht.1]
        congr 1
        simp only [Complex.sub_re]
        ring
      calc
        _ = (2^(-s.re)*Real.Gamma s.re)*
            (t^(a.re-1)*t^(-s.re))*(1-t)^(b.re-1) := by ring
        _ = _ := by rw [he]; ring

theorem spectralBetaLaplaceKernel_integrable (a b s : ℂ)
    (hs : 0 < s.re) (ha : 0 < (a-s).re) (hb : 0 < b.re) :
    Integrable (fun p : ℝ × ℝ => spectralBetaLaplaceKernel a b s p.1 p.2)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => spectralBetaLaplaceKernel a b s p.1 p.2)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    unfold spectralBetaLaplaceKernel spectralUnitBetaProfile
    fun_prop
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact spectralBetaLaplaceKernel_slice_integrable a b s hs ht.1
  · apply ((spectralUnitBetaProfile_integrable (a-s) b ha hb).norm.const_mul
      (2^(-s.re)*Real.Gamma s.re)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (spectralBetaLaplaceKernel_integral_norm a b s hs ht).symm

theorem spectralBetaLaplaceKernel_integral (a b s : ℂ)
    (hs : 0 < s.re) (ha : 0 < (a-s).re) (hb : 0 < b.re) :
    (∫ x in Ioi (0 : ℝ), ∫ t in Ioo (0 : ℝ) 1,
      spectralBetaLaplaceKernel a b s t x) =
      (2 : ℂ)^(-s)*Complex.Gamma s*Complex.betaIntegral (a-s) b := by
  rw [integral_integral_swap (f := fun x t : ℝ => spectralBetaLaplaceKernel a b s t x)
    (spectralBetaLaplaceKernel_integrable a b s hs ha hb).swap]
  calc
    _ = ∫ t in Ioo (0 : ℝ) 1,
        ((2 : ℂ)^(-s)*Complex.Gamma s)*spectralUnitBetaProfile (a-s) b t := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro t ht
      exact spectralBetaLaplaceKernel_integral_x a b s hs ht.1
    _ = _ := by rw [integral_const_mul,spectralUnitBetaProfile_integral]

end ArtinMatthews
