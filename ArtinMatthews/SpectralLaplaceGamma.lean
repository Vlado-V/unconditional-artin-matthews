module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine complex-power Laplace convergence and its Gamma value. -/

noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

theorem spectralLaplaceGamma_integrable (s : ℂ) {a : ℝ} (hs : 0 < s.re) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => (x : ℂ)^(s-1)*Complex.exp (-(a : ℂ)*(x : ℂ))) (Ioi (0 : ℝ)) := by
  have hbase : MellinConvergent (fun x : ℝ => Complex.exp (-(x : ℂ))) s := by
    have hg := Complex.GammaIntegral_convergent hs
    simpa only [MellinConvergent,smul_eq_mul,Complex.ofReal_exp,Complex.ofReal_neg,mul_comm] using hg
  have h := (MellinConvergent.comp_mul_left (f := fun x : ℝ => Complex.exp (-(x : ℂ))) (s := s) ha).mpr hbase
  simpa only [MellinConvergent,smul_eq_mul,Complex.ofReal_mul,neg_mul] using h

theorem spectralLaplaceGamma_integral (s : ℂ) {a : ℝ} (hs : 0 < s.re) (ha : 0 < a) :
    (∫ x in Ioi (0 : ℝ), (x : ℂ)^(s-1)*Complex.exp (-(a : ℂ)*(x : ℂ))) =
      (1/(a : ℂ))^s*Complex.Gamma s := by
  simpa only [neg_mul] using! Complex.integral_cpow_mul_exp_neg_mul_Ioi hs ha

theorem spectralRealLaplaceGamma_integrable {s a : ℝ} (hs : 0 < s) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => x^(s-1)*Real.exp (-a*x)) (Ioi (0 : ℝ)) := by
  have h := (spectralLaplaceGamma_integrable (s : ℂ) (a := a) hs ha).norm
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hx,Complex.norm_exp]
  simp only [Complex.sub_re,Complex.ofReal_re,Complex.one_re,Complex.mul_re,
    Complex.neg_re,Complex.ofReal_im,mul_zero,sub_zero]

end ArtinMatthews
