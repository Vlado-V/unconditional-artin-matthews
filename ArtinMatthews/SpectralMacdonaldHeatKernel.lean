module

public import ArtinMatthews.SpectralMacdonaldConvolution
public import ArtinMatthews.SpectralKLPhysicalDilation


set_option backward.privateInPublic true
@[expose] public section

/-! The positive heat representation of the genuine order-zero K kernel.
The integral and its absolute convergence are derived from Schlaefli. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein
open scoped Topology

namespace ArtinMatthews

def spectralMacdonaldHeatKernel (R r : ℝ) : ℂ :=
  (r : ℂ)⁻¹*Complex.exp (-(r : ℂ)/2-(R : ℂ)^2/(2*r))

theorem spectralMacdonaldHeatKernel_scaled (R : ℝ) {u : ℝ} (_hu : 0 < u) :
    (2 : ℂ)*spectralMacdonaldHeatKernel R (2*u) =
      (u : ℂ)^(-1 : ℂ)*Complex.exp (-(u : ℂ)-(R : ℂ)^2/(4*u)) := by
  unfold spectralMacdonaldHeatKernel
  rw [Complex.cpow_neg_one]
  push_cast
  have he : -(2*(u : ℂ))/2-(R : ℂ)^2/(2*(2*(u : ℂ))) =
      -(u : ℂ)-(R : ℂ)^2/(4*(u : ℂ)) := by ring
  rw [he]
  field_simp

theorem spectralMacdonaldHeatKernel_integrable {R : ℝ} (hR : 0 < R) :
    IntegrableOn (spectralMacdonaldHeatKernel R) (Ioi (0 : ℝ)) := by
  have hi := schlafliIntegral_integrable_all_orders (0 : ℂ) R hR
  simp only [zero_sub] at hi
  have hscaled : IntegrableOn (fun u : ℝ => (2 : ℂ)*spectralMacdonaldHeatKernel R (2*u)) (Ioi (0 : ℝ)) := by
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (spectralMacdonaldHeatKernel_scaled R hu).symm
  have hi' := hscaled.const_mul (1/2 : ℂ)
  have hi'' : IntegrableOn (fun u : ℝ => spectralMacdonaldHeatKernel R (2*u)) (Ioi (0 : ℝ)) := by
    apply hi'.congr
    filter_upwards with u
    ring
  have h := (integrableOn_Ioi_comp_mul_left_iff (spectralMacdonaldHeatKernel R) 0 (by norm_num : (0 : ℝ) < 2)).mp hi''
  simpa only [mul_zero] using h

theorem spectralMacdonaldHeatKernel_integral {R : ℝ} (_hR : 0 < R) :
    (∫ r in Ioi (0 : ℝ), spectralMacdonaldHeatKernel R r) = 2*schlafliBesselK 0 R := by
  have h := integral_comp_mul_left_Ioi' (spectralMacdonaldHeatKernel R) 0 (by norm_num : (0 : ℝ) < 2)
  simp only [mul_zero,Complex.real_smul] at h
  rw [← integral_const_mul] at h
  calc
    _ = ∫ u in Ioi (0 : ℝ), (u : ℂ)^(-1 : ℂ)*Complex.exp (-(u : ℂ)-(R : ℂ)^2/(4*u)) := by
      rw [← h]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact spectralMacdonaldHeatKernel_scaled R hu
    _ = _ := by
      unfold schlafliBesselK schlafliIntegral
      simp only [neg_zero,zero_sub,Complex.cpow_zero,mul_one]
      ring

theorem spectralMacdonaldHeatKernel_re_eq_norm (R : ℝ) {r : ℝ} (hr : 0 < r) :
    (spectralMacdonaldHeatKernel R r).re = ‖spectralMacdonaldHeatKernel R r‖ := by
  have he : -(r : ℂ)/2-(R : ℂ)^2/(2*r) = ((-r/2-R^2/(2*r) : ℝ) : ℂ) := by push_cast; rfl
  have hreal : spectralMacdonaldHeatKernel R r =
      ((r⁻¹*Real.exp (-r/2-R^2/(2*r)) : ℝ) : ℂ) := by
    unfold spectralMacdonaldHeatKernel
    rw [he,← Complex.ofReal_exp,← Complex.ofReal_inv,← Complex.ofReal_mul]
  rw [hreal,Complex.ofReal_re,Complex.norm_real,Real.norm_of_nonneg]
  positivity

end ArtinMatthews
