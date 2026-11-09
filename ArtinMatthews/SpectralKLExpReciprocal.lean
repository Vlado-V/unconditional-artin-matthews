module

public import ArtinMatthews.SpectralMacdonaldHeatKernel
public import ArtinMatthews.SpectralKLPhysicalCompactData


set_option backward.privateInPublic true
@[expose] public section

/-! Actual noncompact Gaussian-Weyl physical profiles.  Their two tails
are integrable by the genuine Schlaefli heat integral. -/

noncomputable section
open Set MeasureTheory Filter

namespace ArtinMatthews

def spectralKLExpReciprocal (a b x : ℝ) : ℂ :=
  if 0 < x then Complex.exp (-(a : ℂ)*(x : ℂ)-(b : ℂ)/(x : ℂ)) else 0

theorem spectralExpReciprocal_div_integrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun x : ℝ => Complex.exp (-(a : ℂ)*(x : ℂ)-(b : ℂ)/(x : ℂ))/(x : ℂ))
      (Ioi (0 : ℝ)) := by
  let R : ℝ := 2*Real.sqrt (a*b)
  have hR : 0 < R := mul_pos two_pos (Real.sqrt_pos.mpr (mul_pos ha hb))
  have hR2 : (R : ℂ)^2 = 4*(a : ℂ)*(b : ℂ) := by
    have hr : R^2 = 4*a*b := by dsimp [R]; rw [mul_pow,Real.sq_sqrt (mul_pos ha hb).le]; ring
    exact_mod_cast hr
  have hs := (integrableOn_Ioi_comp_mul_left_iff (spectralMacdonaldHeatKernel R) 0
    (mul_pos two_pos ha)).mpr (by simpa only [mul_zero] using spectralMacdonaldHeatKernel_integrable hR)
  apply (hs.const_mul ((2*a : ℝ) : ℂ)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  unfold spectralMacdonaldHeatKernel
  have he : -(((2*a)*x : ℝ) : ℂ)/2-(R : ℂ)^2/(2*(((2*a)*x : ℝ) : ℂ)) =
      -(a : ℂ)*(x : ℂ)-(b : ℂ)/(x : ℂ) := by
    rw [hR2]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr ha.ne',Complex.ofReal_ne_zero.mpr hx.ne']
    ring
  rw [he]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr ha.ne',Complex.ofReal_ne_zero.mpr hx.ne']

theorem spectralKLExpReciprocal_measurable (a b : ℝ) : Measurable (spectralKLExpReciprocal a b) := by
  unfold spectralKLExpReciprocal
  apply Measurable.ite measurableSet_Ioi <;> fun_prop

theorem spectralKLExpReciprocal_integrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Integrable (spectralKLExpReciprocal a b) spectralKLPhysicalMeasure := by
  apply (spectralKLPositiveWeightMeasure_complex_integrable_iff (fun x => x⁻¹) _
    (by fun_prop) (fun x hx => inv_nonneg.mpr hx.le)).mpr
  apply (spectralExpReciprocal_div_integrable ha hb).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  change 0 < x at hx
  rw [spectralKLExpReciprocal,ite_eq_left hx,Complex.ofReal_inv]
  ring

theorem spectralKLExpReciprocal_memLp {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    MemLp (spectralKLExpReciprocal a b) 2 spectralKLPhysicalMeasure := by
  apply (memLp_two_iff_integrable_sq_norm
    (spectralKLExpReciprocal_measurable a b).aestronglyMeasurable).mpr
  rw [spectralKLPhysicalMeasure,spectralKLPositiveWeightMeasure_integrable_iff _ _
    (by fun_prop) (fun x hx => inv_nonneg.mpr hx.le)]
  have hi := (spectralExpReciprocal_div_integrable (mul_pos two_pos ha) (mul_pos two_pos hb)).norm
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  change 0 < x at hx
  rw [spectralKLExpReciprocal,ite_eq_left hx,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx,
    Complex.norm_exp,Complex.norm_exp]
  have he (A B : ℝ) : (-(A : ℂ)*(x : ℂ)-(B : ℂ)/(x : ℂ)).re = -A*x-B/x := by
    have h : -(A : ℂ)*(x : ℂ)-(B : ℂ)/(x : ℂ) = ((-A*x-B/x : ℝ) : ℂ) := by push_cast; rfl
    rw [h,Complex.ofReal_re]
  rw [he,he,pow_two,← Real.exp_add]
  have hexp : -(2*a)*x-(2*b)/x = (-a*x-b/x)+(-a*x-b/x) := by ring
  rw [hexp]
  ring

end ArtinMatthews
