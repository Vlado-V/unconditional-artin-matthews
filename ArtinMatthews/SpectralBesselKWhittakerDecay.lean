module

public import ArtinMatthews.SpectralBesselKDecay
public import ArtinMatthews.SpectralBesselKWhittaker


set_option backward.privateInPublic true
@[expose] public section

/-! Tail control of the actual square-root scaled imaginary-order K solution. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectralKBesselWhittaker_norm (ν : ℂ) (q y : ℝ) (hy : 0 < y) :
    ‖spectralKBesselWhittaker ν q y‖ = Real.sqrt y * ‖schlafliBesselK ν (q * y)‖ := by
  rw [spectralKBesselWhittaker_eq_sqrt ν q y hy.le, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg y)]

theorem spectralKBesselWhittaker_deriv_norm_le (ν : ℂ) (q y : ℝ)
    (hq : 0 < q) (hy : 0 < y) :
    ‖deriv (spectralKBesselWhittaker ν q) y‖ ≤ Real.sqrt y *
      (q * ‖deriv (schlafliBesselK ν) (q * y)‖ +
        (1 / (2 * y)) * ‖schlafliBesselK ν (q * y)‖) := by
  have hp : (y : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt y : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hy.le]
    norm_num
  rw [spectralKBesselWhittaker_deriv ν q y hq hy,
    spectralScaledBesselK_deriv ν q y hq hy, hp, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg y)]
  calc
    _ ≤ Real.sqrt y * (‖(q : ℂ) * deriv (schlafliBesselK ν) (q * y)‖ +
        ‖(1 / 2 : ℂ) / y * spectralScaledBesselK ν q y‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.sqrt_nonneg y)
    _ = _ := by
      rw [norm_mul, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
      have hn : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
      rw [hn]
      unfold spectralScaledBesselK
      ring

theorem spectralKBesselWhittaker_imaginary_bound (ν : ℂ) (hν : ν.re = 0)
    (q y : ℝ) (hq : 0 < q) (hy : 1 ≤ y) :
    ‖spectralKBesselWhittaker ν q y‖ ≤
      (spectralSchlafliDecayConstant 0 q / 2) * (y * Real.exp (-(q * y) / 2)) := by
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hb := schlafliBesselK_imaginary_exponential_bound ν hν q (q * y) hq
    (by nlinarith)
  have hs : Real.sqrt y ≤ y := Real.sqrt_le_self_iff.mpr (Or.inr hy)
  rw [spectralKBesselWhittaker_norm ν q y hy0]
  calc
    _ ≤ y * ‖schlafliBesselK ν (q * y)‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg _)
    _ ≤ y * ((spectralSchlafliDecayConstant 0 q / 2) * Real.exp (-(q * y) / 2)) :=
      mul_le_mul_of_nonneg_left hb hy0.le
    _ = _ := by ring

theorem spectralKBesselWhittaker_imaginary_weighted_deriv_bound (ν : ℂ) (hν : ν.re = 0)
    (q y : ℝ) (hq : 0 < q) (hy : 1 ≤ y) :
    y * ‖deriv (spectralKBesselWhittaker ν q) y‖ ≤
      ((q ^ 2 * spectralSchlafliDecayConstant (-1) q / 4) * y ^ 3 +
        (‖ν‖ * spectralSchlafliDecayConstant 0 q / 2) * y ^ 2 +
        (spectralSchlafliDecayConstant 0 q / 4) * y) * Real.exp (-(q * y) / 2) := by
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hqy : q ≤ q * y := by nlinarith
  have hK := schlafliBesselK_imaginary_exponential_bound ν hν q (q * y) hq hqy
  have hD := schlafliBesselK_imaginary_deriv_bound ν hν q (q * y) hq hqy
  have hs : Real.sqrt y ≤ y := Real.sqrt_le_self_iff.mpr (Or.inr hy)
  calc
    _ ≤ y * (Real.sqrt y *
        (q * ‖deriv (schlafliBesselK ν) (q * y)‖ +
          (1 / (2 * y)) * ‖schlafliBesselK ν (q * y)‖)) :=
      mul_le_mul_of_nonneg_left (spectralKBesselWhittaker_deriv_norm_le ν q y hq hy0) hy0.le
    _ ≤ y * (y * (q * ‖deriv (schlafliBesselK ν) (q * y)‖ +
        (1 / (2 * y)) * ‖schlafliBesselK ν (q * y)‖)) := by gcongr
    _ ≤ y * (y * (q * (((1 / 2 : ℝ) *
        (((q * y) / 2) * spectralSchlafliDecayConstant (-1) q +
          (‖ν‖ / q) * spectralSchlafliDecayConstant 0 q)) * Real.exp (-(q * y) / 2)) +
        (1 / (2 * y)) *
          ((spectralSchlafliDecayConstant 0 q / 2) * Real.exp (-(q * y) / 2)))) := by
      gcongr
    _ = _ := by field_simp; ring

theorem spectral_polynomial_exp_tendsto (q : ℝ) (hq : 0 < q) (n : ℕ) :
    Tendsto (fun y : ℝ => y ^ n * Real.exp (-(q * y) / 2)) atTop (𝓝 0) := by
  convert tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) (q / 2)
    (by positivity) using 1
  simp only [Real.rpow_natCast]
  ext y
  congr 2
  ring

theorem spectralKBesselWhittaker_imaginary_tendsto_atTop (ν : ℂ) (hν : ν.re = 0)
    (q : ℝ) (hq : 0 < q) :
    Tendsto (spectralKBesselWhittaker ν q) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hlim := (spectral_polynomial_exp_tendsto q hq 1).const_mul
    (spectralSchlafliDecayConstant 0 q / 2)
  simp only [pow_one, mul_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
  exact spectralKBesselWhittaker_imaginary_bound ν hν q y hq hy

theorem spectralKBesselWhittaker_imaginary_weighted_deriv_tendsto (ν : ℂ) (hν : ν.re = 0)
    (q : ℝ) (hq : 0 < q) :
    Tendsto (fun y : ℝ => y * ‖deriv (spectralKBesselWhittaker ν q) y‖) atTop (𝓝 0) := by
  have hlim := ((spectral_polynomial_exp_tendsto q hq 3).const_mul
    (q ^ 2 * spectralSchlafliDecayConstant (-1) q / 4)).add
    ((spectral_polynomial_exp_tendsto q hq 2).const_mul
      (‖ν‖ * spectralSchlafliDecayConstant 0 q / 2)) |>.add
    ((spectral_polynomial_exp_tendsto q hq 1).const_mul (spectralSchlafliDecayConstant 0 q / 4))
  simp only [mul_zero, add_zero, pow_one] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
    exact mul_nonneg hy (norm_nonneg _)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    have h := spectralKBesselWhittaker_imaginary_weighted_deriv_bound ν hν q y hq hy
    convert h using 1
    ring

end ArtinMatthews
