module

public import ArtinMatthews.SpectralGamma0PoincareTrueWidthKL
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import ArtinMatthews.SpectralWeylCosineKernel


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Gaussian cosine integral, with its absolute convergence
and literal half-line normalization. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace ArtinMatthews

theorem spectralGaussianCosine_integrable {p : ℝ} (hp : 0 < p) (b : ℝ) :
    Integrable (fun u : ℝ => Real.exp (-p*u^2)*Real.cos (b*u)) := by
  apply (integrable_exp_neg_mul_sq hp).mono' (by fun_prop)
  filter_upwards with u
  rw [norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le,Real.norm_eq_abs]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)

theorem spectralGaussianCosine_full {p : ℝ} (hp : 0 < p) (b : ℝ) :
    (∫ u : ℝ, Real.exp (-p*u^2)*Real.cos (b*u)) =
      Real.sqrt (Real.pi/p)*Real.exp (-(b^2)/(4*p)) := by
  let F : ℝ → ℂ := fun u => Complex.exp (-(p : ℂ)*(u : ℂ)^2+((b : ℂ)*Complex.I)*(u : ℂ)+0)
  have hi : Integrable F := integrable_cexp_quadratic (b := (p : ℂ)) hp _ _
  have h := integral_cexp_quadratic (b := -(p : ℂ)) (by simpa using neg_neg_of_pos hp)
    ((b : ℂ)*Complex.I) 0
  have hs : ((Real.pi : ℂ)/(p : ℂ))^(1/2 : ℂ) = (Real.sqrt (Real.pi/p) : ℂ) := by
    rw [← Complex.ofReal_div,
      show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_cpow (div_pos Real.pi_pos hp).le,← Real.sqrt_eq_rpow]
  have hR : (∫ u : ℝ, F u).re = Real.sqrt (Real.pi/p)*Real.exp (-(b^2)/(4*p)) := by
    change (∫ u : ℝ, Complex.exp (-(p : ℂ)*(u : ℂ)^2+((b : ℂ)*Complex.I)*(u : ℂ)+0)).re = _
    rw [h]
    rw [neg_neg,hs]
    have he : (0 : ℂ)-((b : ℂ)*Complex.I)^2/(4* -(p : ℂ)) = ((-(b^2)/(4*p) : ℝ) : ℂ) := by
      push_cast
      rw [mul_pow,Complex.I_sq]
      ring
    rw [he,← Complex.ofReal_exp,← Complex.ofReal_mul,Complex.ofReal_re]
  change RCLike.re (∫ u : ℝ, F u) = _ at hR
  rw [← integral_re hi] at hR
  convert hR using 1
  apply integral_congr_ae
  filter_upwards with u
  have he : -(p : ℂ)*(u : ℂ)^2+((b : ℂ)*Complex.I)*(u : ℂ)+0 =
      ((-p*u^2 : ℝ) : ℂ)+((b*u : ℝ) : ℂ)*Complex.I := by push_cast; ring
  dsimp only [F]
  rw [he]
  change _ = (Complex.exp (((-p*u^2 : ℝ) : ℂ)+((b*u : ℝ) : ℂ)*Complex.I)).re
  rw [Complex.exp_re]
  norm_num [pow_two,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im]

theorem spectralGaussianCosine_Ioi {p : ℝ} (hp : 0 < p) (b : ℝ) :
    (2 : ℝ)*(∫ u in Ioi (0 : ℝ), Real.exp (-p*u^2)*Real.cos (b*u)) =
      Real.sqrt (Real.pi/p)*Real.exp (-(b^2)/(4*p)) := by
  let f : ℝ → ℝ := fun u => Real.exp (-p*u^2)*Real.cos (b*u)
  have hi : Integrable f := spectralGaussianCosine_integrable hp b
  have hn : (∫ u in Iic (0 : ℝ), f u) = ∫ u in Ioi (0 : ℝ), f u := by
    calc
      _ = ∫ u in Ioi (0 : ℝ), f (-u) := by
        simpa only [neg_zero] using (integral_comp_neg_Ioi (0 : ℝ) f).symm
      _ = _ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u _
        simp only [f,neg_sq,mul_neg,Real.cos_neg]
  have h := spectralGaussianCosine_full hp b
  rw [← intervalIntegral.integral_Iic_add_Ioi hi.restrict hi.restrict,hn] at h
  simpa only [two_mul] using h

end ArtinMatthews
