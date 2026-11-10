module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import ArtinMatthews.SpectralGaussianMellin
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

/-! Positive real Gaussian moments used for the absolute-series majorant. -/

noncomputable section
open Set MeasureTheory Filter

namespace ArtinMatthews

theorem spectralGaussianRealMoment_integrable {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => x^(2*a-1)*Real.exp (-x^2)) (Ioi (0 : ℝ)) := by
  have hi := (spectralGaussianMellin_integrable (2*(a : ℂ))
    (by norm_num; linarith) (p := 1) (by norm_num)).norm
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hx,Complex.norm_exp]
  norm_num [Complex.mul_re]
  simp only [← Complex.ofReal_pow,Complex.ofReal_re,true_or]

theorem spectralGaussianRealMoment {a : ℝ} (ha : 0 < a) :
    (∫ x in Ioi (0 : ℝ), x^(2*a-1)*Real.exp (-x^2)) = (1/2 : ℝ)*Real.Gamma a := by
  apply Complex.ofReal_injective
  have hcast : ((∫ x in Ioi (0 : ℝ), x^(2*a-1)*Real.exp (-x^2) : ℝ) : ℂ) =
      ∫ x in Ioi (0 : ℝ), ((x^(2*a-1)*Real.exp (-x^2) : ℝ) : ℂ) := by
    symm
    simpa only using! (integral_complex_ofReal (f := fun x : ℝ => x^(2*a-1)*Real.exp (-x^2))
      (μ := volume.restrict (Ioi (0 : ℝ))))
  rw [hcast]
  calc
    _ = ∫ x in Ioi (0 : ℝ), (x : ℂ)^(2*(a : ℂ)-1)*
        Complex.exp (-(1 : ℂ)*(x : ℂ)^2) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [Complex.ofReal_mul,Complex.ofReal_exp,Complex.ofReal_cpow hx.le]
      push_cast
      ring_nf
    _ = (1/2 : ℂ)*Complex.Gamma (a : ℂ) := by
      have h := spectralGaussianMellin_integral (2*(a : ℂ)) (p := 1)
        (by norm_num; linarith) (by norm_num)
      rw [show 2*(a : ℂ)/2 = a by ring] at h
      simpa only [Complex.ofReal_one,one_div,inv_one,Complex.one_cpow,mul_one,mul_assoc] using! h
    _ = _ := by rw [Complex.Gamma_ofReal]; push_cast; rfl

end ArtinMatthews
