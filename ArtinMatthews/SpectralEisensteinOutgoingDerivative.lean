module

public import ArtinMatthews.SpectralEisensteinOutgoingApproximation


set_option backward.privateInPublic true
@[expose] public section

/-! The upper-height truncation has a uniform weighted derivative bound by
the same actual outgoing envelope as its values. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace ArtinMatthews

theorem eisensteinOutgoingApprox_deriv (q : ℂ) (A t : ℝ) (ht : 0<t) :
    deriv (eisensteinOutgoingApprox q A) t =
      ((deriv eisensteinHeightCutoff t*(1-eisensteinHeightCutoff (A*t)) -
        eisensteinHeightCutoff t*A*deriv eisensteinHeightCutoff (A*t):ℝ):ℂ)*(t:ℂ)^q+
      ((eisensteinHeightCutoff t*(1-eisensteinHeightCutoff (A*t)):ℝ):ℂ)*
        (q*(t:ℂ)^(q-1)) := by
  have hd (u : ℝ) : HasDerivAt eisensteinHeightCutoff (deriv eisensteinHeightCutoff u) u :=
    (eisensteinHeightCutoff_contDiff.differentiable (by simp)).differentiableAt.hasDerivAt
  have hc := (hd t).mul (((hd (A*t)).comp t ((hasDerivAt_id t).const_mul A)).const_sub 1)
  have he := hc.ofReal_comp.mul (eisensteinPositivePower_hasDerivAt q t ht)
  have he' : HasDerivAt (eisensteinOutgoingApprox q A)
      (((deriv eisensteinHeightCutoff t*(1-eisensteinHeightCutoff (A*t)) -
        eisensteinHeightCutoff t*A*deriv eisensteinHeightCutoff (A*t):ℝ):ℂ)*(t:ℂ)^q+
      ((eisensteinHeightCutoff t*(1-eisensteinHeightCutoff (A*t)):ℝ):ℂ)*
        (q*(t:ℂ)^(q-1))) t := by
    convert he using 1
    · rfl
    · simp only [Pi.mul_apply,Function.comp_apply,mul_one]
      push_cast
      ring
  exact he'.deriv

theorem eisensteinOutgoingApprox_weighted_deriv (q : ℂ) (A t : ℝ) (ht : 0<t) :
    (t:ℂ)*deriv (eisensteinOutgoingApprox q A) t =
      ((((t*deriv eisensteinHeightCutoff t)*(1-eisensteinHeightCutoff (A*t)):ℝ):ℂ)
       - ((eisensteinHeightCutoff t*((A*t)*deriv eisensteinHeightCutoff (A*t)):ℝ):ℂ)
       + q*((eisensteinHeightCutoff t*(1-eisensteinHeightCutoff (A*t)):ℝ):ℂ))*(t:ℂ)^q := by
  rw [eisensteinOutgoingApprox_deriv q A t ht,
    Complex.cpow_sub q 1 (Complex.ofReal_ne_zero.mpr ht.ne'),Complex.cpow_one]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr ht.ne']

theorem eisensteinOutgoingApprox_weighted_deriv_le (q : ℂ) (A t M : ℝ)
    (hM : 0≤M) (hb : ∀ u : ℝ, |u*deriv eisensteinHeightCutoff u|≤M) (ht : 0<t) :
    ‖(t:ℂ)*deriv (eisensteinOutgoingApprox q A) t‖ ≤
      (1+M+‖q‖)*eisensteinOutgoingEnvelopeProfile q t := by
  have hχ := (eisensteinHeightCutoff_range t).1
  have hη : |1-eisensteinHeightCutoff (A*t)|≤1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (eisensteinHeightCutoff_range (A*t)).2)]
    exact sub_le_self _ (eisensteinHeightCutoff_range (A*t)).1
  have h1 : ‖(((t*deriv eisensteinHeightCutoff t)*(1-eisensteinHeightCutoff (A*t)):ℝ):ℂ)‖ ≤
      |t*deriv eisensteinHeightCutoff t| := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) hη
  have h2 : ‖((eisensteinHeightCutoff t*((A*t)*deriv eisensteinHeightCutoff (A*t)):ℝ):ℂ)‖ ≤
      eisensteinHeightCutoff t*M := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_nonneg hχ]
    exact mul_le_mul_of_nonneg_left (hb _) hχ
  have h3 : ‖q*((eisensteinHeightCutoff t*(1-eisensteinHeightCutoff (A*t)):ℝ):ℂ)‖ ≤
      ‖q‖*eisensteinHeightCutoff t := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_nonneg hχ]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hχ hη) (norm_nonneg _)
  rw [eisensteinOutgoingApprox_weighted_deriv q A t ht,norm_mul,
    eisensteinOutgoingEnvelopeProfile]
  conv_rhs => rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  refine (norm_add_le _ _).trans ((add_le_add (norm_sub_le _ _) le_rfl).trans ?_)
  refine (add_le_add (add_le_add h1 h2) h3).trans ?_
  have hD := abs_nonneg (t*deriv eisensteinHeightCutoff t)
  nlinarith [mul_nonneg hM hD,mul_nonneg (norm_nonneg q) hD]

end ArtinMatthews
