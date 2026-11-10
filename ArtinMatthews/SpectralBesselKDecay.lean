module

public import ArtinMatthews.SpectralBesselKEquation
public import ArtinMatthews.SpectralBesselKDerivative
public import ArtinMatthews.SpectralBesselKConvergence
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

/-! Exponential bounds for the actual Schläfli integral and Bessel K, including
the imaginary orders occurring in the positive cusp spectrum. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectral_schlafli_scaled_real_majorant (r a c t : ℝ)
    (hc : 0 < c) (ht : 0 < t) (n : ℕ) :
    t ^ (r - 1) * Real.exp (-a * t - c / t) ≤
      ((n.factorial : ℝ) / c ^ n) *
        (t ^ ((r + n) - 1) * Real.exp (-a * t)) := by
  calc
    _ = (t ^ (r - 1) * Real.exp (-a * t)) * Real.exp (-c / t) := by
      rw [show -a * t - c / t = -a * t + (-c / t) by ring, Real.exp_add]
      ring
    _ ≤ (t ^ (r - 1) * Real.exp (-a * t)) *
        ((n.factorial : ℝ) / c ^ n * t ^ n) :=
      mul_le_mul_of_nonneg_left (spectral_exp_neg_div_le_pow c t hc ht n)
        (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_nonneg _))
    _ = _ := by
      rw [show (r + (n : ℝ)) - 1 = (r - 1) + n by ring,
        Real.rpow_add ht, Real.rpow_natCast]
      ring

theorem spectral_schlafli_scaled_real_integrable (r a c : ℝ)
    (ha : 0 < a) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t ^ (r - 1) * Real.exp (-a * t - c / t))
      (Ioi 0) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (-r)
  have hs : -1 < (r + (n : ℝ)) - 1 := by linarith
  have hi : IntegrableOn
      (fun t : ℝ => t ^ ((r + n) - 1) * Real.exp (-a * t)) (Ioi 0) := by
    simpa only [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (r + n) - 1) (p := 1)
        (b := a) hs zero_lt_one ha)
  apply (hi.const_mul ((n.factorial : ℝ) / c ^ n)).mono'
  · fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_nonneg _))]
    exact spectral_schlafli_scaled_real_majorant r a c t hc ht n

def spectralSchlafliDecayConstant (r δ : ℝ) : ℝ :=
  ∫ t : ℝ in Ioi 0, t ^ (r - 1) * Real.exp (-(1 / 2 : ℝ) * t - (δ ^ 2 / 8) / t)

theorem spectralSchlafliDecayConstant_nonneg (r δ : ℝ) :
    0 ≤ spectralSchlafliDecayConstant r δ := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_nonneg _)

theorem spectralSchlafliKernel_exponential_bound (ν : ℂ) (δ x t : ℝ)
    (hδ : 0 < δ) (hx : δ ≤ x) (ht : 0 < t) :
    ‖spectralSchlafliKernel ν x t‖ ≤ Real.exp (-x / 2) *
      (t ^ (ν.re - 1) * Real.exp (-(1 / 2 : ℝ) * t - (δ ^ 2 / 8) / t)) := by
  rw [spectralSchlafliKernel, spectral_schlafli_kernel_norm ν x t ht]
  have hxp : 0 < x := hδ.trans_le hx
  have hsq : δ ^ 2 ≤ x ^ 2 := (sq_le_sq₀ hδ.le hxp.le).mpr hx
  have hyoung : x / 2 - t / 2 ≤ x ^ 2 / (8 * t) :=
    (le_div_iff₀ (by positivity : 0 < 8 * t)).mpr (by nlinarith [sq_nonneg (x - 2 * t)])
  have hδdiv : δ ^ 2 / (8 * t) ≤ x ^ 2 / (8 * t) :=
    div_le_div_of_nonneg_right hsq (by positivity)
  have he : Real.exp (-t - (x ^ 2 / 4) / t) ≤
      Real.exp (-x / 2) * Real.exp (-(1 / 2 : ℝ) * t - (δ ^ 2 / 8) / t) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hxdiv : (x ^ 2 / 4) / t = 2 * (x ^ 2 / (8 * t)) := by ring
    have hddiv : (δ ^ 2 / 8) / t = δ ^ 2 / (8 * t) := by ring
    rw [hxdiv, hddiv]
    linarith
  calc
    _ ≤ t ^ (ν.re - 1) * (Real.exp (-x / 2) *
        Real.exp (-(1 / 2 : ℝ) * t - (δ ^ 2 / 8) / t)) :=
      mul_le_mul_of_nonneg_left he (Real.rpow_nonneg ht.le _)
    _ = _ := by ring

theorem schlafliIntegral_exponential_bound (ν : ℂ) (δ x : ℝ)
    (hδ : 0 < δ) (hx : δ ≤ x) :
    ‖schlafliIntegral ν x‖ ≤
      spectralSchlafliDecayConstant ν.re δ * Real.exp (-x / 2) := by
  have hi := spectral_schlafli_scaled_real_integrable ν.re (1 / 2) (δ ^ 2 / 8)
    (by norm_num) (by positivity)
  have hn : IntegrableOn (fun t => ‖spectralSchlafliKernel ν x t‖) (Ioi 0) :=
    (schlafliIntegral_integrable_all_orders ν x (hδ.trans_le hx)).norm
  have hm : IntegrableOn (fun t => Real.exp (-x / 2) *
      (t ^ (ν.re - 1) * Real.exp (-(1 / 2 : ℝ) * t - (δ ^ 2 / 8) / t)))
      (Ioi 0) := hi.const_mul _
  have hb := integral_mono_ae hn hm (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact spectralSchlafliKernel_exponential_bound ν δ x t hδ hx ht)
  rw [integral_const_mul] at hb
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ), ‖spectralSchlafliKernel ν x t‖ :=
      norm_integral_le_integral_norm _
    _ ≤ _ := by simpa only [spectralSchlafliDecayConstant, mul_comm] using hb

theorem schlafliBesselK_norm (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    ‖schlafliBesselK ν x‖ =
      (1 / 2 : ℝ) * (x / 2) ^ (-ν.re) * ‖schlafliIntegral ν x‖ := by
  rw [schlafliBesselK, norm_mul, norm_mul]
  have hp : (x / 2 : ℂ) = ((x / 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [hp, Complex.norm_cpow_eq_rpow_re_of_pos (show 0 < x / 2 by positivity)]
  simp only [Complex.neg_re]
  norm_num

theorem schlafliBesselK_exponential_bound (ν : ℂ) (δ x : ℝ)
    (hδ : 0 < δ) (hx : δ ≤ x) :
    ‖schlafliBesselK ν x‖ ≤
      ((1 / 2 : ℝ) * (x / 2) ^ (-ν.re) * spectralSchlafliDecayConstant ν.re δ) *
        Real.exp (-x / 2) := by
  rw [schlafliBesselK_norm ν x (hδ.trans_le hx)]
  calc
    _ ≤ ((1 / 2 : ℝ) * (x / 2) ^ (-ν.re)) *
        (spectralSchlafliDecayConstant ν.re δ * Real.exp (-x / 2)) :=
      mul_le_mul_of_nonneg_left (schlafliIntegral_exponential_bound ν δ x hδ hx)
        (mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith) _))
    _ = _ := by ring

theorem schlafliBesselK_imaginary_exponential_bound (ν : ℂ) (hν : ν.re = 0)
    (δ x : ℝ) (hδ : 0 < δ) (hx : δ ≤ x) :
    ‖schlafliBesselK ν x‖ ≤
      (spectralSchlafliDecayConstant 0 δ / 2) * Real.exp (-x / 2) := by
  simpa only [hν, neg_zero, Real.rpow_zero, mul_one, div_eq_mul_inv, mul_comm, one_mul]
    using schlafliBesselK_exponential_bound ν δ x hδ hx

theorem spectralSchlafliPrefactor_norm (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    ‖spectralSchlafliPrefactor ν x‖ = (1 / 2 : ℝ) * (x / 2) ^ (-ν.re) := by
  rw [spectralSchlafliPrefactor, norm_mul]
  have hp : (x / 2 : ℂ) = ((x / 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [hp, Complex.norm_cpow_eq_rpow_re_of_pos (show 0 < x / 2 by positivity)]
  simp only [Complex.neg_re]
  norm_num

theorem schlafliBesselK_imaginary_deriv_bound (ν : ℂ) (hν : ν.re = 0)
    (δ x : ℝ) (hδ : 0 < δ) (hx : δ ≤ x) :
    ‖deriv (schlafliBesselK ν) x‖ ≤
      ((1 / 2 : ℝ) * ((x / 2) * spectralSchlafliDecayConstant (-1) δ +
        (‖ν‖ / δ) * spectralSchlafliDecayConstant 0 δ)) * Real.exp (-x / 2) := by
  have hxp : 0 < x := hδ.trans_le hx
  have hb0 := schlafliIntegral_exponential_bound ν δ x hδ hx
  have hb1 := schlafliIntegral_exponential_bound (ν - 1) δ x hδ hx
  simp only [hν, Complex.sub_re, Complex.one_re, zero_sub] at hb0 hb1
  have hd : ‖ν‖ / x ≤ ‖ν‖ / δ :=
    div_le_div_of_nonneg_left (norm_nonneg ν) hδ hx
  have h1 := mul_le_mul_of_nonneg_left hb1 (by positivity : 0 ≤ x / 2)
  have h2 := mul_le_mul hd hb0 (norm_nonneg (schlafliIntegral ν x))
    (div_nonneg (norm_nonneg ν) hδ.le)
  rw [schlafliBesselK_deriv ν x hxp, norm_mul,
    spectralSchlafliPrefactor_norm ν x hxp, hν, neg_zero, Real.rpow_zero, mul_one,
    schlafliIntegral_deriv ν x hxp]
  calc
    _ ≤ (1 / 2 : ℝ) * (‖-((x : ℂ) / 2) * schlafliIntegral (ν - 1) x‖ +
        ‖ν / (x : ℂ) * schlafliIntegral ν x‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
    _ = (1 / 2 : ℝ) * ((x / 2) * ‖schlafliIntegral (ν - 1) x‖ +
        (‖ν‖ / x) * ‖schlafliIntegral ν x‖) := by
      rw [norm_mul, norm_mul, norm_neg, norm_div, norm_div, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hxp]
      norm_num
    _ ≤ (1 / 2 : ℝ) * ((x / 2) *
        (spectralSchlafliDecayConstant (-1) δ * Real.exp (-x / 2)) +
        (‖ν‖ / δ) * (spectralSchlafliDecayConstant 0 δ * Real.exp (-x / 2))) :=
      mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by norm_num)
    _ = _ := by ring

theorem schlafliBesselK_imaginary_tendsto_atTop (ν : ℂ) (hν : ν.re = 0) :
    Tendsto (schlafliBesselK ν) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have he : Tendsto (fun x : ℝ => Real.exp (-x / 2)) atTop (𝓝 0) := by
    convert tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0 : ℝ) (1 / 2)
      (by norm_num) using 1
    simp only [Real.rpow_zero, one_mul]
    ext x
    congr 1
    ring
  have hlim := he.const_mul (spectralSchlafliDecayConstant 0 1 / 2)
  simp only [mul_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  exact schlafliBesselK_imaginary_exponential_bound ν hν 1 x (by norm_num) hx

theorem schlafliBesselK_imaginary_deriv_tendsto_atTop (ν : ℂ) (hν : ν.re = 0) :
    Tendsto (fun x : ℝ => deriv (schlafliBesselK ν) x) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have he : Tendsto (fun x : ℝ => Real.exp (-x / 2)) atTop (𝓝 0) := by
    convert tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0 : ℝ) (1 / 2)
      (by norm_num) using 1
    simp only [Real.rpow_zero, one_mul]
    ext x
    congr 1
    ring
  have hxe : Tendsto (fun x : ℝ => x * Real.exp (-x / 2)) atTop (𝓝 0) := by
    convert tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) (1 / 2)
      (by norm_num) using 1
    simp only [Real.rpow_one]
    ext x
    congr 2
    ring
  have hlim := (hxe.const_mul (spectralSchlafliDecayConstant (-1) 1 / 4)).add
    (he.const_mul ((‖ν‖ / 2) * spectralSchlafliDecayConstant 0 1))
  simp only [mul_zero, add_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have h := schlafliBesselK_imaginary_deriv_bound ν hν 1 x (by norm_num) hx
  convert h using 1
  ring

end ArtinMatthews
