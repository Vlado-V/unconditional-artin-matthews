module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine integrable vertical-line Gamma bound.  Two recurrence steps
and the defining integral give quadratic decay without asymptotic premises. -/

noncomputable section
open Set MeasureTheory Filter

namespace ArtinMatthews

theorem spectral_Gamma_norm_le_real (z : ℂ) (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz,Real.Gamma_eq_integral hz]
  apply (norm_integral_le_integral_norm _).trans_eq
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (Real.exp_pos (-t)),
    Complex.norm_cpow_eq_rpow_re_of_pos ht,Complex.sub_re,Complex.one_re]

theorem spectral_Gamma_quadratic_decay (z : ℂ) (hz : 0 < z.re) :
    ‖Complex.Gamma z‖*(1+z.im^2) ≤
      2*(Real.Gamma z.re+Real.Gamma (z.re+2)) := by
  have hg0 := Real.Gamma_pos_of_pos hz
  have hz2 : 0 < z.re+2 := by linarith
  have hg2 := Real.Gamma_pos_of_pos hz2
  have hbase := spectral_Gamma_norm_le_real z hz
  have hzn : z ≠ 0 := by intro h; simp only [h,Complex.zero_re] at hz; linarith
  have hzn1 : z+1 ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.add_re,Complex.one_re,Complex.zero_re] at he
    linarith
  have hrec : ‖Complex.Gamma (z+2)‖ = ‖z+1‖*‖z‖*‖Complex.Gamma z‖ := by
    rw [show z+2 = (z+1)+1 by ring,Complex.Gamma_add_one (z+1) hzn1,
      Complex.Gamma_add_one z hzn,norm_mul,norm_mul]
    ring
  have hshift : ‖Complex.Gamma (z+2)‖ ≤ Real.Gamma (z.re+2) := by
    have he : (z+2).re = z.re+2 := by norm_num
    simpa only [he] using spectral_Gamma_norm_le_real (z+2) (by rw [he]; exact hz2)
  have him1 : |z.im| ≤ ‖z+1‖ := by
    simpa only [Complex.add_im,Complex.one_im,add_zero] using Complex.abs_im_le_norm (z+1)
  have him0 := Complex.abs_im_le_norm z
  have him : z.im^2 ≤ ‖z+1‖*‖z‖ := by
    simpa only [← sq, sq_abs] using mul_le_mul him1 him0 (abs_nonneg _) (norm_nonneg _)
  have htail : ‖Complex.Gamma z‖*z.im^2 ≤ Real.Gamma (z.re+2) := by
    calc
      _ ≤ ‖Complex.Gamma z‖*(‖z+1‖*‖z‖) :=
        mul_le_mul_of_nonneg_left him (norm_nonneg _)
      _ = ‖Complex.Gamma (z+2)‖ := by rw [hrec]; ring
      _ ≤ _ := hshift
  by_cases ht : z.im^2 ≤ 1
  · nlinarith [norm_nonneg (Complex.Gamma z)]
  · have ht1 : 1 ≤ z.im^2 := le_of_lt (lt_of_not_ge ht)
    have h := mul_le_mul_of_nonneg_left ht1 (norm_nonneg (Complex.Gamma z))
    nlinarith

theorem spectral_Gamma_vertical_continuous (a : ℝ) (ha : 0 < a) :
    Continuous (fun t : ℝ => Complex.Gamma ((a : ℂ)+(t : ℂ)*Complex.I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  apply (Complex.continuousAt_Gamma _ ?_).comp (by fun_prop)
  intro m hm
  have h := congrArg Complex.re hm
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,mul_one,sub_zero,add_zero,
    Complex.neg_re,Complex.natCast_re] at h
  have hm0 : (0 : ℝ) ≤ m := by positivity
  linarith

theorem spectral_Gamma_vertical_integrable (a : ℝ) (ha : 0 < a) :
    Integrable (fun t : ℝ => Complex.Gamma ((a : ℂ)+(t : ℂ)*Complex.I)) := by
  let C := 2*(Real.Gamma a+Real.Gamma (a+2))
  have hI := integrable_inv_one_add_sq.const_mul C
  apply hI.mono' (spectral_Gamma_vertical_continuous a ha).aestronglyMeasurable
  filter_upwards [] with t
  have h := spectral_Gamma_quadratic_decay ((a : ℂ)+(t : ℂ)*Complex.I) (by simpa using ha)
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,mul_one,sub_zero,add_zero,
    Complex.add_im,Complex.mul_im,zero_add] at h
  change ‖Complex.Gamma ((a : ℂ)+(t : ℂ)*Complex.I)‖ ≤ C*(1+t^2)⁻¹
  exact (le_div_iff₀ (by positivity : 0 < 1+t^2)).mpr h

end ArtinMatthews
