module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import ArtinMatthews.ShiftedVoronoiBesselBounds
public import ArtinMatthews.ShiftedVoronoiBesselLaplace


set_option backward.privateInPublic true
@[expose] public section

/-!
# Laplace duality for the Bessel transform of general source functions

An integrable source supported in a bounded positive interval permits an
absolutely convergent Fubini calculation. The kernel is the actual `J₀`, and
the majorant is proved from its factorial series.
-/

noncomputable section
open MeasureTheory Set Filter Complex

namespace ArtinMatthews

/-- The unnormalized order-zero Hankel transform in squared radial variables. -/
def besselZeroTransform (H : ℝ → ℂ) (y : ℝ) : ℂ :=
  ∫ x in Ioi 0, H x * Complex.besselJ 0 (2 * (Real.sqrt (x * y) : ℂ))

theorem bessel_laplace_kernel_integrable (H : ℝ → ℂ) (hHc : Continuous H)
    (hHi : IntegrableOn H (Ioi 0)) (B t : ℝ)
    (hHs : ∀ x, B < x → H x = 0) (ht : B < t) :
    Integrable (fun p : ℝ × ℝ ↦ H p.1 *
      Complex.besselJ 0 (2 * (Real.sqrt (p.1 * p.2) : ℂ)) *
      (Real.exp (-(t * p.2)) : ℂ))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have hm := hHi.norm.mul_prod (integrableOn_exp_mul_Ioi (show B - t < 0 by linarith) 0)
  apply hm.mono' (by fun_prop)
  have hxy : ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))),
      p ∈ (Ioi 0 ×ˢ Ioi 0) := by
    apply (Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_Ioi.prod measurableSet_Ioi)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact ⟨hx, hy⟩
  filter_upwards [hxy] with p hp
  by_cases hz : H p.1 = 0
  · simp [hz]
  have hxB : p.1 ≤ B := le_of_not_gt (fun hh ↦ hz (hHs p.1 hh))
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  calc
    ‖H p.1‖ * ‖Complex.besselJ 0 (2 * (Real.sqrt (p.1 * p.2) : ℂ))‖ *
        Real.exp (-(t * p.2)) ≤
        ‖H p.1‖ * Real.exp (p.1 * p.2) * Real.exp (-(t * p.2)) := by
      gcongr
      exact norm_besselJ_zero_sqrt_le_exp _ (mul_nonneg hp.1.le hp.2.le)
    _ = ‖H p.1‖ * Real.exp ((p.1 - t) * p.2) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ ‖H p.1‖ * Real.exp ((B - t) * p.2) := by
      gcongr
      exact hp.2.le

/-- Absolute convergence of the outer Laplace integral follows from the same
proved product majorant. -/
theorem besselZeroTransform_laplace_integrable (H : ℝ → ℂ) (hHc : Continuous H)
    (hHi : IntegrableOn H (Ioi 0)) (B t : ℝ)
    (hHs : ∀ x, B < x → H x = 0) (ht : B < t) :
    IntegrableOn (fun y ↦ besselZeroTransform H y * (Real.exp (-(t * y)) : ℂ))
      (Ioi 0) := by
  simpa only [IntegrableOn, besselZeroTransform, integral_mul_const] using
    (bessel_laplace_kernel_integrable H hHc hHi B t hHs ht).integral_prod_right

/-- Laplace duality for a general continuous integrable source with bounded
positive support. The Laplace parameter only needs to exceed the support bound. -/
theorem besselZeroTransform_laplace (H : ℝ → ℂ) (hHc : Continuous H)
    (hHi : IntegrableOn H (Ioi 0)) (B t : ℝ) (hB : 0 ≤ B)
    (hHs : ∀ x, B < x → H x = 0) (ht : B < t) :
    (∫ y in Ioi 0, besselZeroTransform H y * (Real.exp (-(t * y)) : ℂ)) =
      ((1 / t : ℝ) : ℂ) * ∫ x in Ioi 0, H x * (Real.exp (-(x / t)) : ℂ) := by
  have hi := bessel_laplace_kernel_integrable H hHc hHi B t hHs ht
  have ht0 : 0 < t := lt_of_le_of_lt hB ht
  calc
    _ = ∫ y in Ioi 0, ∫ x in Ioi 0, H x *
        Complex.besselJ 0 (2 * (Real.sqrt (x * y) : ℂ)) *
          (Real.exp (-(t * y)) : ℂ) := by
      simp only [besselZeroTransform, integral_mul_const]
    _ = ∫ x in Ioi 0, ∫ y in Ioi 0, H x *
        Complex.besselJ 0 (2 * (Real.sqrt (x * y) : ℂ)) *
          (Real.exp (-(t * y)) : ℂ) := integral_integral_swap hi.swap
    _ = ∫ x in Ioi 0, H x *
        (((1 / t * Real.exp (-x / t)) : ℝ) : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [show (fun y : ℝ ↦ H x *
          Complex.besselJ 0 (2 * (Real.sqrt (x * y) : ℂ)) *
            (Real.exp (-(t * y)) : ℂ)) =
          (fun y ↦ H x * ((Real.exp (-(t * y)) : ℂ) *
            Complex.besselJ 0 (2 * (Real.sqrt (x * y) : ℂ)))) by
              funext y; ring,
        integral_const_mul, integral_exp_mul_besselJ_zero_sqrt t x ht0 hx.le]
    _ = _ := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      push_cast
      rw [neg_div]
      ring

end ArtinMatthews
