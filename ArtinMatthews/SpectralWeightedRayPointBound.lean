module

public import ArtinMatthews.SpectralRayPointBound
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.Measurable


set_option backward.privateInPublic true
@[expose] public section

/-! A weighted pointwise estimate on a positive ray from the actual
square integrals of a complex function and its derivative. -/

noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

theorem spectral_weighted_norm_sq_point_bound (n : ℕ) (hn : 1 ≤ n)
    (a : ℝ) (ha : 0 < a) (f : ℝ → ℂ)
    (hf : ∀ y, a ≤ y → DifferentiableAt ℝ f y)
    (hfi : IntegrableOn (fun y : ℝ => y^n*‖f y‖^2) (Ioi a))
    (hdi : IntegrableOn (fun y : ℝ => y^n*‖deriv f y‖^2) (Ioi a))
    (x : ℝ) (hx : a ≤ x) :
    x^n*‖f x‖^2 ≤ ((n : ℝ)/a+1)*(∫ y in Ioi a,y^n*‖f y‖^2)+
      ∫ y in Ioi a,y^n*‖deriv f y‖^2 := by
  let F : ℝ → ℝ := fun y => y^n*‖f y‖^2
  let H : ℝ → ℝ := fun y => ((n : ℝ)/a+1)*F y+y^n*‖deriv f y‖^2
  have hF : ∀ y, a ≤ y → HasDerivAt F
      ((n : ℝ)*y^(n-1)*‖f y‖^2+y^n*(2*inner ℝ (f y) (deriv f y))) y := by
    intro y hy
    convert! ((hasDerivAt_id y).pow n).mul ((hf y hy).hasDerivAt.norm_sq) using 1
    simp only [Pi.pow_apply,id_eq,mul_one]
  have hbound : ∀ y, a < y → |deriv F y| ≤ H y := by
    intro y hy
    have hy0 : 0 < y := ha.trans hy
    have hyPow : 0 ≤ y^n := pow_nonneg hy0.le n
    have hweight : a*y^(n-1) ≤ y^n := by
      have he : y^(n-1)*y = y^n := by rw [← pow_succ,Nat.sub_add_cancel hn]
      calc
        _ ≤ y*y^(n-1) := mul_le_mul_of_nonneg_right hy.le (pow_nonneg hy0.le (n-1))
        _ = _ := by rw [mul_comm,he]
    have hscale : (n : ℝ)*y^(n-1) ≤ ((n : ℝ)/a)*y^n := by
      calc
        _ = ((n : ℝ)/a)*(a*y^(n-1)) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hweight (by positivity)
    have hnorm : 2*|inner ℝ (f y) (deriv f y)| ≤ ‖f y‖^2+‖deriv f y‖^2 := by
      have hh := abs_real_inner_le_norm (f y) (deriv f y)
      nlinarith [sq_nonneg (‖f y‖-‖deriv f y‖)]
    rw [(hF y hy.le).deriv]
    calc
      _ ≤ |(n : ℝ)*y^(n-1)*‖f y‖^2|+|y^n*(2*inner ℝ (f y) (deriv f y))| := abs_add_le _ _
      _ = (n : ℝ)*y^(n-1)*‖f y‖^2+y^n*(2*|inner ℝ (f y) (deriv f y)|) := by
        rw [abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)*y^(n-1)*‖f y‖^2),
          abs_mul,abs_of_nonneg hyPow,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ (((n : ℝ)/a)*y^n)*‖f y‖^2+y^n*(‖f y‖^2+‖deriv f y‖^2) :=
        add_le_add (mul_le_mul_of_nonneg_right hscale (sq_nonneg _))
          (mul_le_mul_of_nonneg_left hnorm hyPow)
      _ = H y := by dsimp only [H,F];ring
  have hHi : IntegrableOn H (Ioi a) := (hfi.const_mul _).add hdi
  have hDF : IntegrableOn (deriv F) (Ioi a) := by
    apply hHi.mono' (measurable_deriv F).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    simpa only [Real.norm_eq_abs] using hbound y hy
  have hpoint := spectral_ray_point_bound a F H
    (fun y hy => (hF y hy).differentiableAt.hasDerivAt) hfi hDF hHi hbound x hx
  calc
    _ = |F x| := by rw [abs_of_nonneg];exact mul_nonneg (pow_nonneg (ha.le.trans hx) n) (sq_nonneg _)
    _ ≤ ∫ y in Ioi a,H y := hpoint
    _ = _ := by
      dsimp only [H,F]
      rw [integral_add (hfi.const_mul _) hdi,integral_const_mul]

end ArtinMatthews
