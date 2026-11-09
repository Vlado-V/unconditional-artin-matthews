module

public import ArtinMatthews.SpectralUnitBeta
public import ArtinMatthews.SpectralBesselPoissonSeries
public import Mathlib.MeasureTheory.Integral.DominatedConvergence


set_option backward.privateInPublic true
@[expose] public section

/-! Termwise integration of the exponential against an arbitrary integrable
weight on the compact unit interval. -/
noncomputable section
namespace ArtinMatthews

open MeasureTheory Set intervalIntegral Complex NormedSpace Filter
open scoped BigOperators

/-- A genuine dominated-convergence interchange, with a summable exponential
majorant and no assumption about the resulting integral. -/
theorem spectral_exp_unit_weight_integral_hasSum (w : ℝ → ℂ)
    (hw : IntervalIntegrable w volume 0 1) (x : ℂ) :
    HasSum (fun n : ℕ => x ^ n / (n.factorial : ℂ) *
      ∫ u : ℝ in (0 : ℝ)..1, (u : ℂ) ^ n * w u)
      (∫ u : ℝ in (0 : ℝ)..1, Complex.exp (x * u) * w u) := by
  let F : ℕ → ℝ → ℂ := fun n u => (x ^ n / (n.factorial : ℂ)) * (u : ℂ) ^ n * w u
  let B : ℕ → ℝ → ℝ := fun n u => (‖x‖ ^ n / (n.factorial : ℝ)) * ‖w u‖
  have hmeas : ∀ n, AEStronglyMeasurable (F n) (volume.restrict (uIoc (0 : ℝ) 1)) := by
    intro n
    exact (show Measurable (fun u : ℝ => (x ^ n / (n.factorial : ℂ)) * (u : ℂ) ^ n)
      by fun_prop).aestronglyMeasurable.mul hw.def'.aestronglyMeasurable
  have hbound : ∀ n, ∀ᵐ u : ℝ, u ∈ uIoc (0 : ℝ) 1 → ‖F n u‖ ≤ B n u := by
    intro n
    filter_upwards [] with u hu
    have hmod : ‖(u : ℂ)‖ ≤ 1 := by
      have hu' : 0 < u ∧ u ≤ 1 := by simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1), mem_Ioc] using hu
      simpa only [Complex.norm_real, Real.norm_eq_abs,abs_of_nonneg hu'.1.le] using hu'.2
    change ‖x ^ n / (n.factorial : ℂ) * (u : ℂ) ^ n * w u‖ ≤ _
    simp only [norm_mul, norm_div, norm_pow, Complex.norm_natCast]
    calc
      _ ≤ (‖x‖ ^ n / (n.factorial : ℝ) * 1) * ‖w u‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (pow_le_one₀ (norm_nonneg _) hmod) (by positivity)) (norm_nonneg _)
      _ = _ := by simp only [mul_one, B]
  have hsum : ∀ᵐ u : ℝ, u ∈ uIoc (0 : ℝ) 1 → Summable (fun n => B n u) := by
    filter_upwards [] with u _
    exact (expSeries_div_summable ‖x‖).mul_right ‖w u‖
  have hint : IntervalIntegrable (fun u => ∑' n, B n u) volume 0 1 := by
    simpa only [B, tsum_mul_right] using
      hw.norm.const_mul (∑' n : ℕ, ‖x‖ ^ n / (n.factorial : ℝ))
  have hlim : ∀ᵐ u : ℝ, u ∈ uIoc (0 : ℝ) 1 →
      HasSum (fun n => F n u) (Complex.exp (x * u) * w u) := by
    filter_upwards [] with u _
    have hh := (expSeries_div_hasSum_exp (x * (u : ℂ))).mul_right (w u)
    simpa only [F, Complex.exp_eq_exp_ℂ, mul_pow, div_eq_mul_inv,
      mul_assoc, mul_comm, mul_left_comm] using hh
  have hh := intervalIntegral.hasSum_integral_of_dominated_convergence B hmeas hbound hsum hint hlim
  convert hh using 1
  funext n
  simp only [F, mul_assoc, intervalIntegral.integral_const_mul]

end ArtinMatthews
