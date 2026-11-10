module

public import ArtinMatthews.SpectralBesselKDerivative
public import ArtinMatthews.SpectralBesselKConvergence
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

/-! A Gaussian moment detects the actual Schläfli integral and proves that
the imaginary-order K solution is nonzero somewhere on the positive axis. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectralSchlafliKernel_even (ν : ℂ) (x t : ℝ) :
    spectralSchlafliKernel ν (-x) t = spectralSchlafliKernel ν x t := by
  simp only [spectralSchlafliKernel, Complex.ofReal_neg, neg_sq]

theorem spectralSchlafliKernel_gaussian (ν : ℂ) (x t : ℝ) :
    spectralSchlafliKernel ν x t =
      ((t : ℂ) ^ (ν - 1) * Complex.exp (-(t : ℂ))) *
        (Real.exp (-(1 / (4 * t)) * x ^ 2) : ℂ) := by
  rw [spectralSchlafliKernel, Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem spectralSchlafliKernel_norm_gaussian (ν : ℂ) (x t : ℝ) (ht : 0 < t) :
    ‖spectralSchlafliKernel ν x t‖ =
      (t ^ (ν.re - 1) * Real.exp (-t)) * Real.exp (-(1 / (4 * t)) * x ^ 2) := by
  rw [spectralSchlafliKernel, spectral_schlafli_kernel_norm ν x t ht]
  rw [show -t - (x ^ 2 / 4) / t = -t + (-(1 / (4 * t)) * x ^ 2) by ring,
    Real.exp_add]
  ring

theorem spectral_gaussian_reciprocal_integral (t : ℝ) (ht : 0 < t) :
    (∫ x : ℝ, Real.exp (-(1 / (4 * t)) * x ^ 2)) =
      2 * Real.sqrt Real.pi * Real.sqrt t := by
  rw [integral_gaussian]
  have he : Real.pi / (1 / (4 * t)) = (Real.pi * 4) * t := by field_simp
  rw [he, Real.sqrt_mul (by positivity : 0 ≤ Real.pi * 4),
    Real.sqrt_mul Real.pi_pos.le]
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : 0 ≤ (2 : ℝ))]
  ring

theorem spectralSchlafliKernel_slice_integrable (ν : ℂ) (t : ℝ) (ht : 0 < t) :
    Integrable (fun x : ℝ => spectralSchlafliKernel ν x t) := by
  have hg : Integrable (fun x : ℝ => (Real.exp (-(1 / (4 * t)) * x ^ 2) : ℂ)) :=
    (integrable_exp_neg_mul_sq (by positivity : 0 < 1 / (4 * t))).ofReal
  simpa only [spectralSchlafliKernel_gaussian] using
    hg.const_mul ((t : ℂ) ^ (ν - 1) * Complex.exp (-(t : ℂ)))

theorem spectralSchlafliKernel_integral_norm (ν : ℂ) (t : ℝ) (ht : 0 < t) :
    (∫ x : ℝ, ‖spectralSchlafliKernel ν x t‖) =
      (2 * Real.sqrt Real.pi) * (Real.exp (-t) * t ^ ((ν.re + 1 / 2) - 1)) := by
  simp_rw [spectralSchlafliKernel_norm_gaussian ν _ t ht]
  rw [integral_const_mul, spectral_gaussian_reciprocal_integral t ht]
  rw [Real.sqrt_eq_rpow t]
  have hp : t ^ (ν.re - 1) * t ^ (1 / 2 : ℝ) = t ^ ((ν.re + 1 / 2) - 1) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  calc
    _ = (2 * Real.sqrt Real.pi) * (Real.exp (-t) *
        (t ^ (ν.re - 1) * t ^ (1 / 2 : ℝ))) := by ring
    _ = _ := by rw [hp]

theorem spectralSchlafliKernel_product_integrable (ν : ℂ) (hν : -1 / 2 < ν.re) :
    Integrable (fun p : ℝ × ℝ => spectralSchlafliKernel ν p.2 p.1)
      ((volume.restrict (Ioi 0)).prod volume) := by
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => spectralSchlafliKernel ν p.2 p.1)
      ((volume.restrict (Ioi 0)).prod volume) := by
    unfold spectralSchlafliKernel
    fun_prop
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact spectralSchlafliKernel_slice_integrable ν t ht
  · have hgamma := (Real.GammaIntegral_convergent (by linarith : 0 < ν.re + 1 / 2)).const_mul
      (2 * Real.sqrt Real.pi)
    apply hgamma.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (spectralSchlafliKernel_integral_norm ν t ht).symm

theorem spectralSchlafliKernel_integral (ν : ℂ) (t : ℝ) (ht : 0 < t) :
    (∫ x : ℝ, spectralSchlafliKernel ν x t) =
      (2 * Real.sqrt Real.pi : ℂ) *
        ((t : ℂ) ^ ((ν + 1 / 2) - 1) * Complex.exp (-(t : ℂ))) := by
  simp_rw [spectralSchlafliKernel_gaussian]
  rw [integral_const_mul, integral_complex_ofReal, spectral_gaussian_reciprocal_integral t ht]
  have hp : (t : ℂ) ^ (ν - 1) * (Real.sqrt t : ℂ) = (t : ℂ) ^ ((ν + 1 / 2) - 1) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow ht.le]
    push_cast
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht.ne')]
    congr 1
    ring
  push_cast
  calc
    _ = (2 * Real.sqrt Real.pi : ℂ) *
        (((t : ℂ) ^ (ν - 1) * (Real.sqrt t : ℂ)) * Complex.exp (-(t : ℂ))) := by ring
    _ = _ := by rw [hp]

theorem schlafliIntegral_gaussian_moment (ν : ℂ) (hν : -1 / 2 < ν.re) :
    (∫ x : ℝ, schlafliIntegral ν x) =
      (2 * Real.sqrt Real.pi : ℂ) * Complex.Gamma (ν + 1 / 2) := by
  have hi := spectralSchlafliKernel_product_integrable ν hν
  calc
    _ = ∫ t in Ioi (0 : ℝ), ∫ x : ℝ, spectralSchlafliKernel ν x t :=
      (integral_integral_swap hi).symm
    _ = ∫ t in Ioi (0 : ℝ), (2 * Real.sqrt Real.pi : ℂ) *
        ((t : ℂ) ^ ((ν + 1 / 2) - 1) * Complex.exp (-(t : ℂ))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact spectralSchlafliKernel_integral ν t ht
    _ = _ := by
      have hs : 0 < (ν + 1 / 2 : ℂ).re := by norm_num; linarith
      rw [integral_const_mul, Complex.Gamma_eq_integral hs, Complex.GammaIntegral]
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun t => by
        dsimp only
        rw [Complex.ofReal_exp, Complex.ofReal_neg]
        ring

theorem schlafliIntegral_even (ν : ℂ) (x : ℝ) :
    schlafliIntegral ν (-x) = schlafliIntegral ν x := by
  apply integral_congr_ae
  exact Eventually.of_forall fun t => spectralSchlafliKernel_even ν x t

theorem schlafliIntegral_exists_ne_zero (ν : ℂ) (hν : -1 / 2 < ν.re) :
    ∃ x : ℝ, 0 < x ∧ schlafliIntegral ν x ≠ 0 := by
  have hm : (∫ x : ℝ, schlafliIntegral ν x) ≠ 0 := by
    rw [schlafliIntegral_gaussian_moment ν hν]
    apply mul_ne_zero
    · exact mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr Real.pi_pos))
    · apply Complex.Gamma_ne_zero_of_re_pos
      norm_num
      linarith
  by_contra h
  push Not at h
  apply hm
  apply integral_eq_zero_of_ae
  filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · exact (schlafliIntegral_even ν x).symm.trans (h (-x) (neg_pos.mpr hxneg))
  · exact h x hxpos

theorem schlafliBesselK_exists_ne_zero (ν : ℂ) (hν : -1 / 2 < ν.re) :
    ∃ x : ℝ, 0 < x ∧ schlafliBesselK ν x ≠ 0 := by
  obtain ⟨x, hx, hF⟩ := schlafliIntegral_exists_ne_zero ν hν
  refine ⟨x, hx, ?_⟩
  unfold schlafliBesselK
  apply mul_ne_zero _ hF
  apply mul_ne_zero (by norm_num)
  apply Complex.cpow_ne_zero_iff.mpr
  exact Or.inl (div_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne') (by norm_num))

theorem schlafliBesselK_imaginary_exists_ne_zero (ν : ℂ) (hν : ν.re = 0) :
    ∃ x : ℝ, 0 < x ∧ schlafliBesselK ν x ≠ 0 :=
  schlafliBesselK_exists_ne_zero ν (by rw [hν]; norm_num)

end ArtinMatthews
