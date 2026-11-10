module

public import ArtinMatthews.SpectralBesselHyperbolicEvaluation
public import ArtinMatthews.SpectralBesselMellinConvergence
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute convergence of the forward-J tail against the actual KL kernel. -/

namespace ArtinMatthews

open MeasureTheory Set OAI.CubicEisenstein

noncomputable section

private theorem schlafliK_measurable (ν : ℂ) : Measurable (schlafliBesselK ν) := by
  have hp : Measurable (fun x : ℝ => (1 / 2 : ℂ) * (x / 2 : ℂ) ^ (-ν)) := by
    fun_prop
  have hm : StronglyMeasurable (fun p : ℝ × ℝ => (p.2 : ℂ) ^ (ν - 1) *
      Complex.exp (-(p.2 : ℂ) - (p.1 : ℂ) ^ 2 / (4 * p.2))) :=
    (by fun_prop : Measurable _).stronglyMeasurable
  unfold schlafliBesselK schlafliIntegral
  exact hp.mul hm.integral_prod_right'.measurable

private theorem schlafliK_zero_ofReal {y : ℝ} (hy : 0 < y) :
    schlafliBesselK 0 y =
      ((1 / 2 * ∫ u : ℝ, Real.exp (-(y * Real.cosh u)) : ℝ) : ℂ) := by
  have h : (fun u : ℝ => spectralKLogKernel 0 y u) =
      fun u => (Real.exp (-(y * Real.cosh u)) : ℂ) := by
    funext u
    simp only [spectralKLogKernel, zero_mul, add_zero, Complex.ofReal_exp]
  rw [schlafliBesselK_hyperbolic_integral 0 hy, h, integral_complex_ofReal]
  push_cast
  rfl

private theorem schlafliK_zero_norm_eq_re {y : ℝ} (hy : 0 < y) :
    ‖schlafliBesselK 0 y‖ = (schlafliBesselK 0 y).re := by
  rw [schlafliK_zero_ofReal hy, Complex.norm_real, Complex.ofReal_re]
  exact Real.norm_of_nonneg (mul_nonneg (by norm_num) (integral_nonneg fun _ => Real.exp_nonneg _))

theorem spectralJTailK_imaginary_norm_le (t : ℝ) {y : ℝ} (hy : 0 < y) :
    ‖schlafliBesselK ((t : ℂ) * Complex.I) y‖ ≤ ‖schlafliBesselK 0 y‖ := by
  have h := norm_integral_le_integral_norm (μ := volume)
    (spectralKLogKernel ((t : ℂ) * Complex.I) y)
  simp only [spectralKLogKernel, Complex.norm_exp, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_zero, add_zero] at h
  rw [schlafliBesselK_hyperbolic_integral _ hy, schlafliK_zero_norm_eq_re hy,
    schlafliK_zero_ofReal hy, Complex.ofReal_re, norm_mul]
  have hh : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num [norm_div]
  rw [hh]
  exact mul_le_mul_of_nonneg_left h (by norm_num)

/-- The Mellin mass furnishing the uniform constant in the tail bound. -/
def spectralJTailKZeroMellinMass : ℝ :=
  ∫ y in Ioi (0 : ℝ), y ^ (-(3 / 4) : ℝ) * ‖schlafliBesselK 0 y‖

theorem spectralJTailKZeroMellinMass_nonneg : 0 ≤ spectralJTailKZeroMellinMass :=
  setIntegral_nonneg measurableSet_Ioi fun _ hy =>
    mul_nonneg (Real.rpow_nonneg (mem_Ioi.mp hy).le _) (norm_nonneg _)

private theorem mellinWeight_integrable :
    IntegrableOn (fun y : ℝ => y ^ (-(3 / 4) : ℝ) * ‖schlafliBesselK 0 y‖) (Ioi 0) := by
  have h := (schlafliBesselK_mellin_integrable 0 (1 / 4) (by norm_num [Complex.div_re])).norm
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (mem_Ioi.mp hy)]
  congr 2
  norm_num [Complex.div_re]

/-- The kernel with respect to Lebesgue measure in both positive variables. -/
def spectralJTailKernel (t y w : ℝ) : ℂ :=
  ((Real.exp (-((w - 1) * y)) * y ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) *
    schlafliBesselK ((t : ℂ) * Complex.I) y

private theorem tailKernel_measurable (t : ℝ) :
    Measurable (fun p : ℝ × ℝ => spectralJTailKernel t p.1 p.2) := by
  have he : Measurable (fun p : ℝ × ℝ =>
      (Real.exp (-((p.2 - 1) * p.1)) * p.1 ^ (-(1 / 2) : ℝ) : ℝ)) := by fun_prop
  unfold spectralJTailKernel
  exact (Complex.continuous_ofReal.measurable.comp he).mul
    ((schlafliK_measurable _).comp measurable_fst)

private theorem tailKernel_norm_le (t : ℝ) {y w : ℝ} (hy : 0 < y) (hw : 1 < w) :
    ‖spectralJTailKernel t y w‖ ≤
      (y ^ (-(3 / 4) : ℝ) * ‖schlafliBesselK 0 y‖) * (w - 1) ^ (-(1 / 4) : ℝ) := by
  have hw' : 0 < w - 1 := sub_pos.mpr hw
  have hu : 0 < (w - 1) * y := mul_pos hw' hy
  have he : Real.exp (-((w - 1) * y)) ≤ ((w - 1) * y) ^ (-(1 / 4) : ℝ) := by
    rw [Real.rpow_def_of_pos hu]
    exact Real.exp_le_exp.mpr (by linarith [Real.log_le_sub_one_of_pos hu])
  rw [Real.mul_rpow hw'.le hy.le] at he
  rw [spectralJTailKernel, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hy.le _))]
  calc
    _ ≤ ((w - 1) ^ (-(1 / 4) : ℝ) * y ^ (-(1 / 4) : ℝ) * y ^ (-(1 / 2) : ℝ)) *
        ‖schlafliBesselK 0 y‖ :=
      mul_le_mul (mul_le_mul_of_nonneg_right he (Real.rpow_nonneg hy.le _))
        (spectralJTailK_imaginary_norm_le t hy) (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [show (-(3 / 4) : ℝ) = -(1 / 4) + -(1 / 2) by norm_num, Real.rpow_add hy]
      ring

theorem spectralJTailKernel_slice_bound (t : ℝ) {w : ℝ} (hw : 1 < w) :
    (∫ y in Ioi (0 : ℝ), ‖spectralJTailKernel t y w‖) ≤
      spectralJTailKZeroMellinMass * (w - 1) ^ (-(1 / 4) : ℝ) := by
  have hm : Measurable (fun y => spectralJTailKernel t y w) :=
    (tailKernel_measurable t).comp (measurable_id.prodMk measurable_const)
  have hb := mellinWeight_integrable.mul_const ((w - 1) ^ (-(1 / 4) : ℝ))
  have hle : ∀ᵐ y ∂volume.restrict (Ioi (0 : ℝ)), ‖spectralJTailKernel t y w‖ ≤
      (y ^ (-(3 / 4) : ℝ) * ‖schlafliBesselK 0 y‖) * (w - 1) ^ (-(1 / 4) : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact tailKernel_norm_le t hy hw
  rw [spectralJTailKZeroMellinMass, ← integral_mul_const]
  exact integral_mono_ae (hb.mono' hm.aestronglyMeasurable hle).norm hb hle

theorem spectralJTailKZero_bound {w : ℝ} (hw : 1 < w) :
    (∫ y in Ioi (0 : ℝ),
        Real.exp (-((w - 1) * y)) * y ^ (-(1 / 2) : ℝ) * (schlafliBesselK 0 y).re) ≤
      spectralJTailKZeroMellinMass * (w - 1) ^ (-(1 / 4) : ℝ) := by
  refine le_trans (le_of_eq ?_) (spectralJTailKernel_slice_bound 0 hw)
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  change Real.exp (-((w - 1) * y)) * y ^ (-(1 / 2) : ℝ) * (schlafliBesselK 0 y).re =
    ‖spectralJTailKernel 0 y w‖
  simp only [spectralJTailKernel, norm_mul, Complex.ofReal_zero, zero_mul, Complex.norm_real]
  rw [Real.norm_of_nonneg (Real.exp_nonneg _),
    Real.norm_of_nonneg (Real.rpow_nonneg (mem_Ioi.mp hy).le _),
    schlafliK_zero_norm_eq_re hy]

private theorem tailShift_preserving :
    MeasurePreserving (fun w : ℝ => w - 1) (volume.restrict (Ioi (2 : ℝ)))
      (volume.restrict (Ioi (1 : ℝ))) := by
  have h := (measurePreserving_add_right (volume : Measure ℝ) (-1)).restrict_preimage
    (s := Ioi (1 : ℝ)) measurableSet_Ioi
  have hs : (fun w : ℝ => w + -1) ⁻¹' Ioi (1 : ℝ) = Ioi (2 : ℝ) := by
    ext w
    simp only [mem_preimage, mem_Ioi]
    constructor <;> intro hw <;> linarith
  simpa only [hs, sub_eq_add_neg] using h

private theorem tailWeight_integrable (B : ℝ) :
    IntegrableOn (fun w : ℝ => B * (w - 1) ^ (-(5 / 4) : ℝ)) (Ioi 2) := by
  have h := (integrableOn_Ioi_rpow_of_lt (a := -(5 / 4 : ℝ)) (c := 1)
    (by norm_num) (by norm_num)).const_mul B
  exact (tailShift_preserving.integrable_comp_emb
    (measurableEmbedding_addRight (-1 : ℝ))).mpr h

private theorem tailWeight_integral (B : ℝ) :
    (∫ w in Ioi (2 : ℝ), B * (w - 1) ^ (-(5 / 4) : ℝ)) = 4 * B := by
  rw [tailShift_preserving.integral_comp (measurableEmbedding_addRight (-1 : ℝ))
    (fun u : ℝ => B * u ^ (-(5 / 4) : ℝ)), integral_const_mul,
    integral_Ioi_rpow_of_lt (by norm_num : -(5 / 4 : ℝ) < -1) (by norm_num)]
  norm_num; ring

/-- The absolute kernel integral is finite using only the one-step tail bound. -/
theorem spectralJTailKernel_pair_integrable_and_bound (F : ℝ → ℂ) (hF : Measurable F)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ w : ℝ, 2 < w → ‖F w‖ ≤ B / w) (t : ℝ) :
    Integrable (fun p : ℝ × ℝ => spectralJTailKernel t p.1 p.2 * F p.2)
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (2 : ℝ)))) ∧
      (∫ y in Ioi (0 : ℝ), ∫ w in Ioi (2 : ℝ), ‖spectralJTailKernel t y w * F w‖) ≤
        4 * spectralJTailKZeroMellinMass * B := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let ν : Measure ℝ := volume.restrict (Ioi 2)
  let K (p : ℝ × ℝ) := spectralJTailKernel t p.1 p.2 * F p.2
  let q (p : ℝ × ℝ) := (p.1 ^ (-(3 / 4) : ℝ) * ‖schlafliBesselK 0 p.1‖) *
    (B * (p.2 - 1) ^ (-(5 / 4) : ℝ))
  have hq : Integrable q (μ.prod ν) := mellinWeight_integrable.mul_prod (tailWeight_integrable B)
  have hd : ∀ᵐ p ∂μ.prod ν, p ∈ Ioi (0 : ℝ) ×ˢ Ioi (2 : ℝ) := by
    apply (Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_Ioi.prod measurableSet_Ioi)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    exact ⟨hy, hw⟩
  have hle : ∀ᵐ p ∂μ.prod ν, ‖K p‖ ≤ q p := by
    filter_upwards [hd] with p hp
    have hy : 0 < p.1 := hp.1
    have hw : 2 < p.2 := hp.2
    have hw' : 0 < p.2 - 1 := by linarith
    have hr : B / p.2 ≤ B / (p.2 - 1) :=
      div_le_div_of_nonneg_left hB hw' (by linarith)
    dsimp only [K, q]
    rw [norm_mul]
    calc
      _ ≤ ((p.1 ^ (-(3 / 4) : ℝ) * ‖schlafliBesselK 0 p.1‖) *
          (p.2 - 1) ^ (-(1 / 4) : ℝ)) * (B / (p.2 - 1)) :=
        mul_le_mul (tailKernel_norm_le t hy (by linarith)) ((hbound _ hw).trans hr)
          (norm_nonneg _) (by positivity)
      _ = _ := by
        rw [show (-(5 / 4) : ℝ) = -(1 / 4) + -1 by norm_num, Real.rpow_add hw',
          Real.rpow_neg_one, div_eq_mul_inv]
        ring
  have hi : Integrable K (μ.prod ν) := hq.mono'
    ((tailKernel_measurable t).mul (hF.comp measurable_snd)).aestronglyMeasurable hle
  refine ⟨hi, ?_⟩
  change (∫ y, ∫ w, ‖K (y, w)‖ ∂ν ∂μ) ≤ _
  calc
    _ = ∫ p, ‖K p‖ ∂μ.prod ν := (integral_prod _ hi.norm).symm
    _ ≤ ∫ p, q p ∂μ.prod ν := integral_mono_ae hi.norm hq hle
    _ = spectralJTailKZeroMellinMass * (∫ w in Ioi (2 : ℝ), B * (w - 1) ^ (-(5 / 4) : ℝ)) :=
      integral_prod_mul (μ := μ) (ν := ν)
        (fun y => y ^ (-(3 / 4) : ℝ) * ‖schlafliBesselK 0 y‖)
        (fun w => B * (w - 1) ^ (-(5 / 4) : ℝ))
    _ = 4 * spectralJTailKZeroMellinMass * B := by
      rw [tailWeight_integral]
      ring

theorem spectralJTailKernel_pair_integrable (F : ℝ → ℂ) (hF : Measurable F)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ w : ℝ, 2 < w → ‖F w‖ ≤ B / w) (t : ℝ) :
    Integrable (fun p : ℝ × ℝ => spectralJTailKernel t p.1 p.2 * F p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (2 : ℝ)))) :=
  (spectralJTailKernel_pair_integrable_and_bound F hF B hB hbound t).1

theorem spectralJTailKernel_integral_swap (F : ℝ → ℂ) (hF : Measurable F)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ w : ℝ, 2 < w → ‖F w‖ ≤ B / w) (t : ℝ) :
    (∫ y in Ioi (0 : ℝ), ∫ w in Ioi (2 : ℝ), spectralJTailKernel t y w * F w) =
      ∫ w in Ioi (2 : ℝ), ∫ y in Ioi (0 : ℝ), spectralJTailKernel t y w * F w :=
  integral_integral_swap (spectralJTailKernel_pair_integrable F hF B hB hbound t)

end
end ArtinMatthews
