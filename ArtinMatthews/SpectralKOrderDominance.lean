module

public import ArtinMatthews.SpectralBesselCoshEvaluation
public import ArtinMatthews.SpectralBesselMellinConvergence
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory OAI.CubicEisenstein
noncomputable section

theorem spectral_norm_cosh_le_real (z : ℂ) : ‖Complex.cosh z‖ ≤ Real.cosh z.re := by
  rw [Complex.cosh, norm_div, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num, Real.cosh_eq]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    _ ≤ ‖Complex.exp z‖ + ‖Complex.exp (-z)‖ := norm_add_le _ _
    _ = _ := by simp only [Complex.norm_exp, Complex.neg_re]

def spectralKRealCoshKernel (β x u : ℝ) : ℝ := Real.exp (-(x * Real.cosh u)) * Real.cosh (β * u)

theorem spectralKCoshKernel_real (β x u : ℝ) :
    spectralKCoshKernel (β : ℂ) x u = (spectralKRealCoshKernel β x u : ℂ) := by
  unfold spectralKCoshKernel spectralKRealCoshKernel
  rw [← Complex.ofReal_mul, ← Complex.ofReal_cosh, ← Complex.ofReal_exp, Complex.ofReal_mul]

theorem spectralKRealCoshKernel_nonneg (β x u : ℝ) : 0 ≤ spectralKRealCoshKernel β x u :=
  mul_nonneg (Real.exp_nonneg _) (Real.cosh_pos _).le

theorem spectralKRealCoshKernel_integrable (β : ℝ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (spectralKRealCoshKernel β x) (Ioi (0 : ℝ)) := by
  have hi := (spectralKCoshKernel_integrable (β : ℂ) hx).norm
  apply hi.congr
  filter_upwards with u
  rw [spectralKCoshKernel_real, Complex.norm_real,
    Real.norm_of_nonneg (spectralKRealCoshKernel_nonneg _ _ _)]

theorem schlafliBesselK_real_nonneg (β : ℝ) {x : ℝ} (hx : 0 < x) :
    schlafliBesselK (β : ℂ) x = ((∫ u in Ioi (0 : ℝ), spectralKRealCoshKernel β x u) : ℝ) := by
  rw [schlafliBesselK_cosh_integral _ hx]
  simp only [spectralKCoshKernel_real]
  exact integral_complex_ofReal

theorem schlafliBesselK_order_norm_le (β : ℝ) (hβ : 0 ≤ β) {ν : ℂ}
    (hν : |ν.re| ≤ β) {x : ℝ} (hx : 0 < x) :
    ‖schlafliBesselK ν x‖ ≤ ‖schlafliBesselK (β : ℂ) x‖ := by
  rw [schlafliBesselK_cosh_integral ν hx, schlafliBesselK_real_nonneg β hx,
    Complex.norm_real, Real.norm_of_nonneg (integral_nonneg (spectralKRealCoshKernel_nonneg β x))]
  apply norm_integral_le_of_norm_le (spectralKRealCoshKernel_integrable β hx)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  change 0 < u at hu
  rw [spectralKCoshKernel, norm_mul, Complex.norm_exp, Complex.ofReal_re]
  unfold spectralKRealCoshKernel
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  apply (spectral_norm_cosh_le_real (ν * (u : ℂ))).trans
  apply Real.cosh_le_cosh.mpr
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    abs_mul, abs_of_nonneg hβ, abs_of_nonneg hu.le]
  exact mul_le_mul_of_nonneg_right hν hu.le

theorem spectralK_power_integrable (β B : ℝ) (hB : |β| < B) :
    IntegrableOn (fun x : ℝ => x ^ (B - 1) * ‖schlafliBesselK (β : ℂ) x‖) (Ioi (0 : ℝ)) := by
  have hs : |((β : ℂ)).re| < ((B : ℂ)).re := by simpa only [Complex.ofReal_re] using hB
  have hi := (schlafliBesselK_mellin_integrable (β : ℂ) (B : ℂ) hs).norm
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [norm_mul, show (B : ℂ) - 1 = ((B - 1 : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.ofReal_re]

end
end ArtinMatthews
